module

public meta import SpytialLean.Evidence
public meta import Aesop.Builder.Forward
public meta import Aesop.Forward.State.Initial
public meta import Aesop.Search.Expansion.Norm

public meta section

namespace SpytialLean

open Lean Meta

private initialize inspectionLimit : InternalExceptionId ←
  registerInternalExceptionId `spytial.inspectionLimit

/-- Run Aesop's normalization engine with forward eliminators and selected rules. A checkpoint
retains the last allowed context when the inspection budget is exhausted. Chaining and the
alternation with simplification belong to Aesop. Returned proofs live in the original scope. -/
def forwardInspectionProofs (facts rules : Array Expr) (simplify : Bool)
    (maxSteps maxHeartbeats : Nat) : MetaM (Array Expr × Bool) :=
  withoutModifyingState <| withInspectionScope facts do
    if maxHeartbeats == 0 then return (#[], true)
    let resultType ← mkFreshExprMVar (mkSort .zero)
    let target ← mkFreshExprSyntheticOpaqueMVar resultType
    let mut hypotheses : Array Hypothesis := #[]
    for fact in facts do
      hypotheses := hypotheses.push {
        userName := ← mkFreshUserName `spytial_premise
        type := ← inferType fact, value := fact
      }
    for rule in rules do
      hypotheses := hypotheses.push {
        userName := ← mkFreshUserName `spytial_rule
        type := ← inferType rule, value := rule, kind := .implDetail
      }
    let (inputs, goal) ← target.mvarId!.assertHypotheses hypotheses
    let ruleSet ← goal.withContext do
      let mut ruleSet : Aesop.LocalRuleSet := ∅
      for name in #[``And.left, ``And.right, ``Classical.choose_spec,
          ``Or.resolve_left, ``Or.resolve_right] do
        ruleSet := ruleSet.add (← Aesop.RuleBuilder.forwardCore (.const name) none none
          (.norm { penalty := 0 }) false)
      for name in #[``Iff.mp, ``Iff.mpr] do
        ruleSet := ruleSet.add (← Aesop.RuleBuilder.forwardCore (.const name)
          (some #[`self]) none (.norm { penalty := 0 }) false)
      for index in [:rules.size] do
        let rule := mkFVar inputs[facts.size + index]!
        let name ← rule.fvarId!.getUserName
        ruleSet := ruleSet.add (← Aesop.RuleBuilder.forwardCore (.term (mkIdent name) rule)
          none none (.norm { penalty := 1 }) false)
      pure ruleSet
    let options : Aesop.Options' := {
      generateScript := false, forwardMaxDepth? := none, maxNormIterations := maxSteps + 2
    }
    let normSimpContext : Aesop.NormSimpContext := {
      toContext := ← Simp.Context.mkDefault
      enabled := simplify, useHyps := false, configStx? := none
      simprocs := #[(← Simp.getSimprocs)]
    }
    let checkpoint ← IO.mkRef (goal, ← saveState)
    let steps ← IO.mkRef 0
    -- This observes Aesop's progress without modifying the goal. Allow one extra successful
    -- step as a probe, then restore the last permitted context instead of losing the prefix.
    let record : Aesop.NormStep := fun current _ _ => do
      let n ← steps.get
      if n > maxSteps then throw <| .internal inspectionLimit
      checkpoint.set (current, ← (show MetaM _ from saveState))
      steps.set (n + 1)
      return .unchanged
    let mvars := Aesop.UnorderedArraySet.ofHashSet (← goal.getMVarDependencies)
    let normSteps := #[record, Aesop.NormStep.runPreSimpRules mvars,
      Aesop.NormStep.simp (.ofArray mvars.toArray), Aesop.NormStep.runPostSimpRules mvars]
    let result? ← tryCatchRuntimeEx (do
      withOptions (·.setBool `aesop.dev.statefulForward true) do
        withTheReader Core.Context (fun c => { c with maxHeartbeats := maxHeartbeats * 1000 }) do
          withCurrHeartbeats do
            let ((fs, ruleMatches), _) ← (ruleSet.mkInitialForwardState goal).run
            let state : Aesop.NormM.State := {
              forwardState := fs
              forwardRuleMatches := (∅ : Aesop.ForwardRuleMatches).update ruleMatches ∅ #[]
            }
            let ((result, _), _) ← Aesop.runNormSteps goal normSteps (by simp [normSteps])
              |>.run { options, ruleSet, normSimpContext }
              |>.run state
              |>.run
            return some result) fun ex => do
        if ex.isMaxHeartbeat then return none
        if let .internal id _ := ex then
          if id == inspectionLimit then return none
        throw ex
    let (enriched, truncated) ← match result? with
      | some (.changed enriched _) => pure (enriched, false)
      | some .unchanged => pure (goal, false)
      | some (.proved _) =>
          if (← steps.get) <= maxSteps then
            -- Closing the placeholder goal only supplies contradiction evidence if its type
            -- is still compatible with False. Never overwrite a type chosen by automation.
            unless ← isDefEq resultType (mkConst ``False) do
              throwError "spytial: Aesop closed an inspection goal at a type other than False"
            let proof ← checkInspectionProof (mkConst ``False) (← instantiateMVars target)
            return (#[proof], false)
          else
            let (saved, state) ← checkpoint.get
            state.restore
            pure (saved, true)
      | none =>
          let (saved, state) ← checkpoint.get
          state.restore
          pure (saved, true)
    let outputs ← enriched.withContext do
      let inputScope := (← goal.getDecl).lctx
      let mut outputs := #[]
      for decl in ← getLCtx do
        unless inputScope.contains decl.fvarId || decl.isImplementationDetail do
          if ← isProp decl.type then outputs := outputs.push (mkFVar decl.fvarId)
      return outputs
    -- Close a copy of the temporary goal with each result. Infer its type after Lean discharges
    -- all introduced hypotheses, including earlier results occurring inside dependent choices.
    let proofs ← outputs.mapM fun proof => withoutModifyingState do
      enriched.assign proof
      let proof ← whnf (← instantiateMVars target)
      let proposition ← inferType proof
      unless ← isDefEq resultType proposition do
        throwError "spytial: exported evidence conflicts with the inspection goal's type"
      checkInspectionProof proposition proof
    return (proofs, truncated)

end SpytialLean

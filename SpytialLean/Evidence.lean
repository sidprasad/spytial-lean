module

public import Lean
meta import Lean.Elab.Tactic.Omega
meta import Lean.Meta.Tactic.Contradiction

namespace SpytialLean

open Lean Meta

/-- Evidence is an ordinary Lean proof term. Check it against the requested proposition in the
current scope before using it to justify a displayed relation or refinement. -/
public meta def checkInspectionProof (proposition proof : Expr) : MetaM Expr := do
  let proof ← instantiateMVars proof
  let proposition ← instantiateMVars proposition
  let checked := mkApp2 (mkConst ``id [.zero]) proposition proof
  if checked.hasExprMVar || checked.hasLevelMVar || checked.hasSorry then
    throwError "spytial: inspection evidence contains unresolved holes or sorry"
  let scope ← instantiateLCtxMVars (← getLCtx)
  match Kernel.check (← getEnv) scope checked with
  | .error exception => throwError "{exception.toMessageData (← getOptions)}"
  | .ok _ => return proof

/-- Keep ambient declarations available for typing, but expose only admitted evidence to tactics
that search the local context. Data instances remain available for rule instantiation; Prop-valued
instances must be admitted evidence. The caller asserts its copies of those proofs in this scope. -/
public meta def withInspectionScope (proofs : Array Expr) (action : MetaM α) : MetaM α := do
  let mut scope ← getLCtx
  for decl in scope do scope := scope.setKind decl.fvarId .implDetail
  let instances ← (← getLocalInstances).filterM fun localInstance => do
    return !(← isProp (← inferType localInstance.fvar)) || proofs.any (· == localInstance.fvar)
  withLCtx scope instances action

/-- Lean's contradiction tactic decides when the retained premises forbid an ordinary diagram.
Excluded ambient hypotheses remain available for typing, but cannot be searched as premises. -/
public meta def inspectionContradiction? (proofs : Array Expr) : MetaM (Option Expr) :=
  withoutModifyingState <| withNewMCtxDepth <| withInspectionScope proofs do
    let target ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
    let hypotheses : Array Hypothesis ← proofs.mapM fun proof => do
      return {
        userName := ← mkFreshUserName `spytial_premise
        type := ← inferType proof, value := proof
      }
    let (_, goal) ← target.mvarId!.assertHypotheses hypotheses
    unless ← goal.contradictionCore {} do return none
    return some (← checkInspectionProof (mkConst ``False) (← instantiateMVars target))

/-- A bounded attempt reports failure to find evidence, never evidence of falsity. -/
public meta inductive ProofAttempt where
  | proved (proof : Expr)
  | notProved
  | truncated

/-- Ask Omega only about the supplied evidence and the negated goal it introduces. Ambient
propositions are not additional premises. The returned proof lives in the caller's scope. -/
public meta def proveArithmetic (proofs : Array Expr) (claim : Expr)
    (maxHeartbeats : Nat := 20_000) : MetaM ProofAttempt :=
  withoutModifyingState <| withNewMCtxDepth do
    if maxHeartbeats == 0 then return .truncated
    tryCatchRuntimeEx (do
      withTheReader Core.Context
          (fun ctx => { ctx with maxHeartbeats := maxHeartbeats * 1000 }) do
        withCurrHeartbeats do
          let scope ← getLCtx
          let target ← mkFreshExprSyntheticOpaqueMVar claim
          if let some goal ← target.mvarId!.falseOrByContra then
            goal.withContext do
              let mut premises := proofs.toList
              for hyp in ← getLocalHyps do
                unless scope.contains hyp.fvarId! do premises := premises ++ [hyp]
              Lean.Elab.Tactic.Omega.omega premises goal
          let proof ← instantiateMVars target
          if proof.hasMVar || proof.hasLevelMVar then return .notProved
          return .proved (← checkInspectionProof claim proof)) fun ex => do
      if ex.isMaxHeartbeat then return .truncated
      match ex with
      | .internal .. => throw ex
      | .error .. => return .notProved

end SpytialLean

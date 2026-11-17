module

public meta import SpytialLean.Context.Forward

namespace SpytialLean

open Lean Meta

public meta section

/-- Controls preparation of one inspection. These are search and presentation choices, not a
definition of all propositions that follow from the Lean context. -/
structure InspectionConfig where
  hypotheses : Array Expr := #[]
  excludedHypotheses : Array FVarId := #[]
  simplify : Bool := false
  rootOnly : Bool := true
  /-- Maximum successful normalization steps in Aesop. -/
  maxSteps : Nat := ({} : Aesop.Options).maxNormIterations
  maxFacts : Nat := 128
  maxHeartbeats : Nat := 20_000

/-- The original scope plus the proof terms available to one inspection. The proposition justified
by a proof is its Lean type; there is no separate "known fact" language. Witnesses are ordinary
choice terms, recorded only so the renderer can share and label their occurrences. -/
structure InspectionContext where
  root : Expr
  scope : LocalContext
  localInstances : LocalInstances
  proofs : Array Expr := #[]
  witnesses : Array Expr := #[]
  truncated : Bool := false
  contradiction? : Option Expr := none

private def propositionOf (proof : Expr) : MetaM Expr := do
  whnf (← instantiateMVars (← inferType proof))

private def sameType (left right : Expr) : MetaM Bool :=
  withoutModifyingState <| withNewMCtxDepth do isDefEq left right

private def hasProposition (proofs : Array Expr) (proposition : Expr) : MetaM Bool := do
  for proof in proofs do
    if ← sameType (← propositionOf proof) proposition then return true
  return false

private def admit (config : InspectionConfig) (ctx : InspectionContext) (proof : Expr) :
    MetaM InspectionContext := do
  let proposition ← propositionOf proof
  if ← hasProposition ctx.proofs proposition then return ctx
  if ctx.proofs.size >= config.maxFacts then return { ctx with truncated := true }
  let proof ← checkInspectionProof (← inferType proof) proof
  return { ctx with proofs := ctx.proofs.push proof }

private partial def bodyEstablished (proofs : Array Expr) (body : Expr) : MetaM Bool := do
  let body ← whnf body
  if body.isAppOfArity ``And 2 then
    return (← bodyEstablished proofs body.getAppArgs[0]!) &&
      (← bodyEstablished proofs body.getAppArgs[1]!)
  for proof in proofs do
    if ← sameType (← inferType proof) body then return true
  return false

/-- Reuse a witness already exposed by the user's proof instead of drawing a duplicate unknown. -/
private def existingWitness? (config : InspectionConfig) (proofs : Array Expr)
    (type predicate : Expr) : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    if decl.isImplementationDetail || config.excludedHypotheses.contains decl.fvarId then continue
    let term := mkFVar decl.fvarId
    if (← sameType decl.type type) && (← bodyEstablished proofs (mkApp predicate term)) then
      return some term
  return none

/-- Aesop can derive a choice body even when presentation reuses a named witness. Omit those
extra anonymous occurrences rather than asserting that the choice equals the named value. -/
private partial def mentionsRedundantWitness (config : InspectionConfig)
    (available : Array Expr) (ctx : InspectionContext) (term : Expr) : MetaM Bool := do
  if term.isAppOfArity ``Classical.choose 3 && !term.hasLooseBVars then
    if ← ctx.witnesses.anyM (sameType term ·) then return false
    let args := term.getAppArgs
    return (← existingWitness? config available args[0]! args[1]!).isSome
  term.foldlM (fun found child =>
    if found then pure true else mentionsRedundantWitness config available ctx child) false

/-- Select display propositions and shared witnesses using Lean eliminators after inference.
An unresolved disjunction is kept whole. -/
private partial def expose (config : InspectionConfig) (available : Array Expr)
    (ctx : InspectionContext) (proof : Expr) : MetaM InspectionContext := do
  let proof ← if config.simplify then
    let (result, _) ← simp (← inferType proof) (← Simp.Context.mkDefault)
      #[(← Simp.getSimprocs)]
    result.mkEqMP proof
  else pure proof
  let proof ← instantiateMVars proof
  let proposition ← propositionOf proof
  if proposition.isAppOfArity ``And 2 then
    let ctx ← expose config available ctx (← mkAppM ``And.left #[proof])
    expose config available ctx (← mkAppM ``And.right #[proof])
  else if proposition.isAppOfArity ``Iff 2 then
    let ctx ← expose config available ctx (← mkAppM ``Iff.mp #[proof])
    expose config available ctx (← mkAppM ``Iff.mpr #[proof])
  else if proposition.isAppOfArity ``Exists 2 then
    let args := proposition.getAppArgs
    if (← existingWitness? config available args[0]! args[1]!).isSome then return ctx
    let witness ← mkAppM ``Classical.choose #[proof]
    let ctx := if ctx.witnesses.contains witness then ctx
      else { ctx with witnesses := ctx.witnesses.push witness }
    let ctx ← expose config available ctx (← mkAppM ``Classical.choose_spec #[proof])
    -- Witnesses are presentation anchors, not an existential certificate. A vacuous binder
    -- needs no atom and no synthetic `Nonempty` fact.
    let used ← ctx.proofs.anyM fun p => do return ((← inferType p).find? (· == witness)).isSome
    return if used then ctx else { ctx with witnesses := ctx.witnesses.filter (· != witness) }
  else admit config ctx proof

private def forwardRules (config : InspectionConfig) : MetaM (Array Expr) := do
  let mut rules := #[]
  for rule in config.hypotheses do
    if rule.isFVar && config.excludedHypotheses.contains rule.fvarId! then continue
    -- `fyi` makes both directions usable as rules. Aesop's structural Iff eliminators only
    -- expose implications as premises; derived implications are not themselves registered rules.
    if (← propositionOf rule).isAppOfArity ``Iff 2 then
      rules := rules.push (← mkAppM ``Iff.mp #[rule])
      rules := rules.push (← mkAppM ``Iff.mpr #[rule])
    else rules := rules.push rule
  return rules

/-- Prepare evidence for inspecting a value or a proof, without changing the caller's proof state.
Proof subjects contribute their own decomposition; value subjects collect permitted local proofs.
Each admitted proof is checked in the original scope. Aesop's temporary hypotheses never escape. -/
def prepareInspectionContext (subject : Expr) (config : InspectionConfig := {}) :
    MetaM InspectionContext := withoutModifyingState <| withNewMCtxDepth do
  let root ← instantiateMVars (← whnf (← instantiateMVars subject))
  if root.hasMVar || root.hasLevelMVar then
    throwError "spytial: the inspected subject contains unresolved metavariables"
  let mut ctx : InspectionContext := {
    root, scope := ← instantiateLCtxMVars (← getLCtx), localInstances := ← getLocalInstances }
  ctx ← withLCtx ctx.scope ctx.localInstances do
    if ← isProp (← inferType root) then admit config ctx root
    else
      let mut initial := ctx
      for decl in ← getLCtx do
        unless decl.isImplementationDetail || config.excludedHypotheses.contains decl.fvarId do
          if ← isProp decl.type then initial ← admit config initial (mkFVar decl.fvarId)
      return initial
  let rules ← forwardRules config
  let premises := ctx.proofs
  let searchInstances := ctx.localInstances.filter fun inst =>
    !config.excludedHypotheses.contains inst.fvar.fvarId!
  let (proofs, truncated) ← withLCtx ctx.scope searchInstances do
    forwardInspectionProofs premises rules config.simplify config.maxSteps config.maxHeartbeats
  -- Keep compound premises available to rules that consume them. Decomposition only chooses
  -- display propositions; it must not replace the context supplied to Aesop.
  -- Witness reuse consults the completed proof collection, not the prefix displayed so far.
  let available := premises ++ proofs
  ctx := { ctx with proofs := #[], truncated := ctx.truncated || truncated }
  for premise in premises do
    ctx ← expose config available ctx premise
  for proof in proofs do
    unless ← mentionsRedundantWitness config available ctx (← inferType proof) do
      ctx ← expose config available ctx proof
  let contradiction? ← withLCtx ctx.scope searchInstances do inspectionContradiction? ctx.proofs
  return { ctx with contradiction? }

end

end SpytialLean

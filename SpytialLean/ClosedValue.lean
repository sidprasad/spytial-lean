module

public import SpytialLean.LosslessIdentity
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.ReifyCore

namespace SpytialLean.ClosedValue

open Lean Meta RelationalizerCore

public meta initialize registerTraceClass `spytial.closedValue

/-!
The closed-value production route evaluates the typed exposure and runs the proved shared engine.
It is selected only when a `LosslessIdentity` certificate is already available and the exposure agrees
with ordinary expression inspection, including the selected identity policy. Unsupported inspection
features stay on the existing expression adapter. Declining this route does not change identities.

The metadata pass below only follows the emitted datum's field references: it cannot allocate atoms
or relations. Its source expressions are selector/provenance metadata, never inputs to `reify`.
The universal proof is about `program`, the pure Lean computation being evaluated. This does not
prove the metaprogram or Lean's compiled evaluator correct; optional concrete-output certification
at the command boundary remains a separate check.
-/

/-- A production datum computed by the universally proved typed program, with inspection metadata.
`roundTrip` proves `reify program = Except.ok value`, not an equality obtained by testing a
decoder. -/
public meta structure Result where
  datum : RootedJsonDataInstance
  program : Expr
  roundTrip : Expr
  provenance : Provenance
  evidence : SelectorEvidence

private meta inductive Source where
  | node (original reduced : Expr) (fields : List (String × Source))

private meta def decline : MetaM α := throwError "not an ordinary certified closed value"

private meta unsafe def evalClosedUnsafe (α : Type) (type value : Expr) : MetaM α :=
  evalExpr α type value

@[implemented_by evalClosedUnsafe]
private meta opaque evalClosed (α : Type) (type value : Expr) : MetaM α

-- Compare with the expression adapter's selected policy, not merely with whichever ValueIdentity
-- instance happens to be available. In particular, `.eqv` is not the same as `.asWritten`.
private meta def selectedKey (type value : Expr) : MetaM (Option IdentityKey) := do
  if let some inst ← synthInstance? (← mkAppM ``SpytialIdentity #[type]) then
    let via ← whnf (← mkAppOptM ``SpytialIdentity.viaOf #[some type, some inst])
    if via.isAppOf ``IdentityVia.asWritten then return none
    unless via.isAppOf ``IdentityVia.identity do decline
    let key ← mkAppOptM ``SpytialIdentity.runtimeKey? #[some type, some inst, some value]
    evalClosed (Option IdentityKey) (mkApp (mkConst ``Option [.zero])
      (mkConst ``IdentityKey)) key
  else
    let some inst ← synthInstance? (← mkAppM ``ToIdentityKey #[type]) | decline
    let key ← mkAppOptM ``ToIdentityKey.toKey #[some type, some inst, some value]
    return some (← evalClosed IdentityKey (mkConst ``IdentityKey) key)

-- Admission inspects structure and policies, but never builds a graph. The finite typed node
-- bounds this traversal. Type tags must also distinguish the Lean types present in this value.
private meta partial def prepare (original : Expr) (node : Node IdentityKey IdentityKey) :
    StateT (Std.HashMap IdentityKey ExprStructEq) MetaM Source := do
  let originalType ← inferType original
  if originalType.isAppOf ``Raw || originalType.isAppOf ``Viewed then liftM decline
  let reduced ← whnf original
  let type ← whnf (← inferType reduced)
  let head := type.getAppFn.constName!
  if (getSpytialRelationalizerName? (← getEnv) head).isSome then liftM decline
  let .value identity typeName label children := node
  let expectedKey ← selectedKey type reduced
  match identity, expectedKey with
  | .asWritten, none => pure ()
  | .keyed typeKey valueKey, some expected =>
      unless valueKey == expected do liftM decline
      if let some previous := (← get)[typeKey]? then
        unless previous.val.equal type do liftM decline
      else modify (·.insert typeKey ⟨type⟩)
  | _, _ => liftM decline
  unless typeName == (← sigOfType type) do liftM decline
  let fields ← match reduced with
    | .lit (.natVal n) =>
        unless label == toString n && children.isEmpty do liftM decline
        pure []
    | .lit (.strVal value) =>
        unless label == "\"" ++ value ++ "\"" && children.isEmpty do liftM decline
        pure []
    | _ =>
        let .const constructor _ := reduced.getAppFn | liftM decline
        let some (.ctorInfo info) := (← getEnv).find? constructor | liftM decline
        unless label == shortName constructor do liftM decline
        let arguments := reduced.getAppArgs.extract info.numParams reduced.getAppArgs.size
        unless arguments.size == children.length do liftM decline
        let names := ctorDataBinderNames info
        let mut fields := []
        for ((name, child), index) in children.zipIdx do
          unless name == fieldRelName (shortName constructor) names index do liftM decline
          let source ← prepare arguments[index]! child
          fields := (name, source) :: fields
        pure fields.reverse
  return .node original reduced fields

-- Reused atoms retain their first representative; aliases are recorded in the same postorder as
-- walkExpr's withSelectorTerm. No source values are decoded from labels.
private meta partial def attach (datum : JsonDataInstance) (root : String) :
    Source → StateT WalkState MetaM Unit
  | .node original reduced fields => do
      unless (← get).provenance.contains root do
        modify fun state => { state with provenance := state.provenance.insert root reduced }
        for (name, child) in fields do
          let .ok childRoot := datum.child root name | liftM decline
          attach datum childRoot child
      modify (·.rememberSelectorTerm original root)

/-- Try the proved route without deriving new identity instances or changing the environment.
Only ordinary closed inspection is admitted; custom renderers, view wrappers, observations,
contextual refinements, and equivalence-decider identities retain their existing adapter. Imported
host definitions need to be available for meta evaluation (`meta import`); otherwise this route
declines too. `trace.spytial.closedValue` explains evaluation and certificate failures. -/
public meta def relationalize? (value : Expr) (cfg : WalkConfig := {})
    (observations : Array Expr := #[]) : MetaM (Option Result) := withoutModifyingEnv do
  unless isClosedValue value && spytial.identity.auto.get (← getOptions) do return none
  unless observations.isEmpty && cfg.observations.isEmpty && !cfg.functionGraphs &&
      !cfg.shareSymbolicValues && cfg.refinements.isEmpty && cfg.observationResults.isEmpty &&
      cfg.observationResiduals.isEmpty && cfg.observationDomain.isNone do return none
  let saved ← saveState
  try
    let type ← whnf (← inferType value)
    let certificateType ← mkAppOptM ``LosslessIdentity #[some type, none, none, none, none]
    let some certificate ← synthInstance? certificateType
      | trace[spytial.closedValue] "no available LosslessIdentity certificate for {type}"
        return none
    let proof ← mkAppOptM ``Structural.reify_relationalize_of_lossless
      #[some type, none, none, none, none, some certificate, some value]
    let proof ← instantiateMVars proof
    checkWithKernel proof
    let program ← instantiateMVars (← mkAppM ``Structural.relationalizeCandidate #[value])
    let exposed ← instantiateMVars (← mkAppM ``StructuralExposure.nodeOf #[value])
    let nodeType ← inferType exposed
    let node ← evalClosed (Node IdentityKey IdentityKey) nodeType exposed
    let (source, _) ← (prepare value node).run {}
    let datum := RelationalizerCore.walk node
    let (_, state) ← (attach datum.data datum.root source).run {}
    return some {
      datum, program, roundTrip := proof
      provenance := state.provenance
      evidence := { terms := state.selectorTerms } }
  catch error =>
    trace[spytial.closedValue] "using expression adapter: {error.toMessageData}"
    saved.restore
    return none

end SpytialLean.ClosedValue

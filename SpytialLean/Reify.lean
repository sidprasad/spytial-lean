module

public import SpytialLean.ReifyCore
public import SpytialLean.ReifyInstances
public import SpytialLean.StructuralExposure
public meta import SpytialLean.ReifyOptions
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.ClosedValue
public meta import Lean.ToExpr
public meta import Lean.Meta.Tactic.Cbv

namespace SpytialLean.Reify

open Lean Elab Meta Term

/-!
# Adapter for the existing relationalizer

The pure `SpytialReify` class is a decoder only. Ordinary closed values with an available
`LosslessIdentity` certificate can now use the proved typed exposure and shared engine directly at
the `#spytial` and `relationalize%` boundaries. `ClosedValue` attaches provenance and selector
aliases by reading that datum, without building another graph. Other cases retain the existing
expression adapter; contextual tactics are unchanged. Both routes return the same ordinary
`JsonDataInstance` format paired with an explicit root atom ID.

`MetaM` belongs only at this adapter boundary: quoting a host value, reducing an elaborated
expression, and discovering its instances require Lean's environment. Decoding the resulting
`RootedJsonDataInstance` with `reify` is pure and typed.

`set_option spytial.certifyReification true` enables kernel-checked reconstruction at the
`#spytial` command and `relationalize%` boundaries. The exact datum already produced by the walk is
checked, without rerunning relationalization or changing its identity policy. This is an opt-in
per-invocation guarantee; it is not a universal proof of the expression adapter. The contextual
`spytial` tactic remains unchanged and is not certified by this option.
-/

/-- Quote a fully instantiated host value and use Spytial's closed-value production route.

The `ToExpr` instance performs only the host-to-expression boundary. In particular, the returned
datum contains no copy of `value` for the decoder to retrieve. Compatible certified values use the
proved typed pipeline; otherwise the expression adapter retains its existing semantics. -/
public meta def relationalizeValue {α : Type u} [ToExpr α]
    (value : α) (config : WalkConfig := {}) : MetaM RootedJsonDataInstance := do
  let expression := toExpr value
  unless isClosedValue expression do
    throwError "spytial reify: expected a closed value"
  if let some result ← ClosedValue.relationalize? expression config then
    return result.datum
  SpytialLean.relationalizeRooted expression config

public meta instance : ToExpr JsonAtom where
  toTypeExpr := mkConst ``JsonAtom
  toExpr atom := mkApp3 (mkConst ``JsonAtom.mk)
    (toExpr atom.id) (toExpr atom.type) (toExpr atom.label)

public meta instance : ToExpr JsonTuple where
  toTypeExpr := mkConst ``JsonTuple
  toExpr tuple := mkApp2 (mkConst ``JsonTuple.mk) (toExpr tuple.atoms) (toExpr tuple.types)

public meta instance : ToExpr JsonRelation where
  toTypeExpr := mkConst ``JsonRelation
  toExpr relation := mkApp4 (mkConst ``JsonRelation.mk) (toExpr relation.id)
    (toExpr relation.name) (toExpr relation.types) (toExpr relation.tuples)

public meta instance : ToExpr JsonDataInstance where
  toTypeExpr := mkConst ``JsonDataInstance
  toExpr data := mkApp2 (mkConst ``JsonDataInstance.mk) (toExpr data.atoms)
    (toExpr data.relations)

public meta instance : ToExpr RootedJsonDataInstance where
  toTypeExpr := mkConst ``RootedJsonDataInstance
  toExpr datum := mkApp2 (mkConst ``RootedJsonDataInstance.mk)
    (toExpr datum.root) (toExpr datum.data)

/-- Prove reconstruction of this exact output of the production walk by establishing
`StructurallyRepresents datum value` and applying the universal reconstruction theorem. Checking the
structural relation avoids imposing an irrelevant ordering on the datum's relation array.

This certifies a successful invocation, not universal correctness or termination of the `MetaM`
adapter. It works with occurrence-preserving or merged graphs. Lossy custom identities fail;
there is no identity fallback, second walk, replacement datum, or native-evaluation proof axiom. -/
public meta def certifyReification (value : Expr) (datum : RootedJsonDataInstance) : MetaM Expr := do
  unless isClosedValue value do
    throwError "spytial reify: certification requires a closed, fully instantiated value"
  try
    let type ← whnf (← inferType value)
    let proposition ← mkAppOptM ``structurallyRepresents
      #[some type, none, none, some (toExpr datum), some value]
    let proposition ← mkEq proposition (mkConst ``Bool.true)
    let goal ← mkFreshExprMVar proposition
    let [decideGoal] ← goal.mvarId!.applyConst ``of_decide_eq_true
      | throwError "could not create the representation proof obligation"
    Lean.Meta.Tactic.Cbv.cbvDecideGoal decideGoal
    let represented ← instantiateMVars goal
    let proof ← mkAppM ``reify_of_structurallyRepresents #[represented]
    let proof ← instantiateMVars proof
    checkWithKernel proof
    return proof
  catch error =>
    throwError "spytial reify: could not certify the emitted datum; the value may be unsupported, \
      irreducible, or lose structure under its identity policy\n{error.toMessageData}"

/-- Check the opted-in guarantee without altering the already-emitted datum or its metadata. -/
public meta def certifyReificationIfRequested (value : Expr) (datum : RootedJsonDataInstance) :
    MetaM Unit := do
  if spytial.certifyReification.get (← getOptions) then
    discard <| certifyReification value datum

/-- Command boundary: certified ordinary closed values use the proved typed pipeline; other
inspection modes retain the expression adapter. Certification, when requested, still checks the
exact emitted datum rather than trusting the compiled evaluation of the pure program. -/
public meta def relationalizeWithEvidence (value : Expr) (config : WalkConfig := {})
    (observations : Array Expr := #[]) :
    MetaM (RootedJsonDataInstance × Provenance × SelectorEvidence) := do
  let result ← match ← ClosedValue.relationalize? value config observations with
    | some result => pure (result.datum, result.provenance, result.evidence)
    | none => SpytialLean.relationalizeRootedWithEvidence value config observations
  certifyReificationIfRequested value result.1
  return result

public section

/-- Relationalize a closed, fully elaborated term during elaboration and embed the resulting
`RootedJsonDataInstance` in a kernel-checked declaration.

For example, a concrete structural reconstruction round trip can be stated directly as:

```lean
theorem example :
    reify (relationalize% (some 7 : Option Nat)) = Except.ok (some 7) := by
  apply reify_of_structurallyRepresents
  decide_cbv
```

With an available `LosslessIdentity` certificate and compatible ordinary inspection semantics, `%`
elaborates directly to the proved pure `Structural.relationalizeCandidate` application. Its round trip
then follows from `Structural.reify_relationalize_of_lossless`, without checking a particular datum.
Other closed values retain the expression adapter and embed its rooted datum. Open terms,
metavariables, universe parameters, and terms containing `sorry` are rejected. Optional
`spytial.certifyReification` additionally checks the concrete datum produced during elaboration.
-/
syntax:max "relationalize% " term:67 : term

elab_rules : term
  | `(relationalize% $value) => do
      let valueExpression ← elabTerm value none
      synthesizeSyntheticMVarsNoPostponing
      let valueExpression ← instantiateMVars valueExpression
      unless isClosedValue valueExpression do
        throwErrorAt value
          "`relationalize%` requires a closed, fully instantiated value without `sorry`"
      if let some result ← ClosedValue.relationalize? valueExpression then
        certifyReificationIfRequested valueExpression result.datum
        return result.program
      let datum ← SpytialLean.relationalizeRooted valueExpression
      certifyReificationIfRequested valueExpression datum
      return toExpr datum

/-- A concrete theorem through the actual relationalizer. The general proof used here is
`reify_of_structurallyRepresents`; `decide_cbv` kernel-checks that this elaboration-time datum has the
independent structural representation of the closed value. -/
public theorem relationalize_nat_roundtrip :
    SpytialLean.reify (relationalize% (37 : Nat)) = Except.ok 37 := by
  apply reify_of_structurallyRepresents
  decide_cbv

end

end SpytialLean.Reify

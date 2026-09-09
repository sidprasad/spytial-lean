module

public import SpytialLean.ReifyCore
public import SpytialLean.ReifyInstances
public meta import SpytialLean.Relationalizer
public meta import Lean.ToExpr

namespace SpytialLean.Reify

open Lean Elab Meta Term

/-!
# Adapter for the existing relationalizer

The pure `SpytialReify` class is a decoder only. This module connects it to the actual
expression-level relationalizer used by `#spytial` and the `spytial` tactic. It returns the same
ordinary `JsonDataInstance` already consumed by Spytial, paired with the root atom ID returned by
that same walk; no parallel encoder or evidence registry is involved.

`MetaM` belongs only at this adapter boundary: quoting a host value, reducing an elaborated
expression, and discovering its instances require Lean's environment. Decoding the resulting
`RootedJsonDataInstance` with `reify` is pure and typed.
-/

/-- Quote a fully instantiated host value and pass it to Spytial's existing relationalizer.

The `ToExpr` instance performs only the host-to-expression boundary. In particular, the returned
datum contains no copy of `value` for the decoder to retrieve. -/
public meta def relationalizeValue {α : Type u} [ToExpr α]
    (value : α) (config : WalkConfig := {}) : MetaM RootedJsonDataInstance := do
  let expression := toExpr value
  unless isClosedValue expression do
    throwError "spytial reify: expected a closed value"
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

public section

/-- Relationalize a closed, fully elaborated term during elaboration and embed the resulting
`RootedJsonDataInstance` in a kernel-checked declaration.

For example, a concrete Tier 1 round trip can be stated directly as:

```lean
theorem example :
    reify (relationalize% (some 7 : Option Nat)) = Except.ok (some 7) := by
  apply reify_of_tier1Represents
  decide_cbv
```

The `%` form is the bridge across the unavoidable `MetaM` boundary: the existing relationalizer
runs while the declaration is elaborated, then only its root ID and ordinary data result remain in
the theorem. Open terms, metavariables, universe parameters, and terms containing `sorry` are
rejected.
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
      return toExpr (← SpytialLean.relationalizeRooted valueExpression)

/-- A concrete theorem through the actual relationalizer. The general proof used here is
`reify_of_tier1Represents`; `decide_cbv` kernel-checks that this elaboration-time datum has the
independent structural representation of the closed value. -/
public theorem relationalize_nat_roundtrip :
    SpytialLean.reify (relationalize% (37 : Nat)) = Except.ok 37 := by
  apply reify_of_tier1Represents
  decide_cbv

end

end SpytialLean.Reify

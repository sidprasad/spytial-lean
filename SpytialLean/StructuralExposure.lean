module

public import SpytialLean.Identity
public import SpytialLean.RelationalizerCore
public import SpytialLean.ReifyCore
public import SpytialLean.StructuralEncoding
public import SpytialLean.StructuralSharing

namespace SpytialLean

/-!
# Typed exposure for the shared relationalization engine

`RelationalizerCore.Engine` is the graph-building state machine. It owns atom allocation, identity
interning, and relation construction. A `StructuralExposure α` exposes an `α` as the structural
nodes consumed by that walker.

The expression adapter in `Relationalizer` discovers the same information from `Lean.Expr` in
`MetaM`. For a supported datatype, `deriving SpytialReify` instead generates an ordinary pattern
matcher from `α` to structural nodes. The generated function is pure; only the deriving handler
that writes it requires `MetaM`.

The typed entry point is consequently just composition with the shared walker:

```text
α --StructuralExposure.expose--> Node --RelationalizerCore.walk--> rooted datum
```

`reify_relationalizeCandidate_of_coherent` proves that this unchecked composition round-trips when
reuse keys reflect constructor/field structure at every reachable occurrence. This is an input
identity law, not an assumption that the output datum already represents the value. The shared
engine's preservation proof establishes that intermediate fact.

The optional `deriving LosslessIdentity` handler proves this identity hypothesis automatically for
concrete supported types. Its round-trip theorem applies to `relationalizeCandidate` below, not
to the checked convenience wrapper.

The convenience function `Structural.relationalize` keeps the normal identity-aware result when
that result structurally represents the input.
If a custom identity merges structurally different values, it sends the same exposed nodes through
the same walker with occurrence-preserving identity. This yields the universal round trip:

```lean
reify (Structural.relationalize x) = Except.ok x
```

Structural reconstruction is a capability defined by the laws of `StructuralReification` and
`StructuralExposure`. Types can supply these instances and proofs directly. `LosslessIdentity`
separately certifies that the selected sharing policy preserves all reachable structure.

Automatic derivation supports primitives plus regular, first-order, non-indexed inductive types
and structures. Data fields may be explicit, implicit, strict-implicit, or instance-implicit;
their Spytial relation names must be distinct within each constructor. Dependent or indexed
families, mutual, nested, and non-regular recursion, and proof-, type-, or function-valued fields
are outside the current deriving handler.
-/

/-- The value-level identity information that typed exposure can pass to the shared walker. -/
public class ValueIdentity (alpha : Type u) where
  key? : alpha → Option IdentityKey

/-- An explicit Spytial identity declaration takes precedence, including `asWritten`. -/
public instance (priority := high) [SpytialIdentity alpha] : ValueIdentity alpha where
  key? value := SpytialIdentity.runtimeKey? value

/-- A primitive or container encoding supplies the default structural identity. -/
public instance (priority := low) [ToIdentityKey alpha] : ValueIdentity alpha where
  key? value := some (ToIdentityKey.toKey value)

/-- Values without a reusable key remain reconstructible occurrence-by-occurrence. -/
public instance (priority := 1) : ValueIdentity alpha where
  key? _ := none

/-- Convert value-level identity into the request understood by the shared engine. -/
@[expose] public def valueIdentity [ValueIdentity alpha]
    (typeKey : IdentityKey) (value : alpha) :
    RelationalizerCore.Identity IdentityKey IdentityKey :=
  match ValueIdentity.key? value with
  | some valueKey => .keyed typeKey valueKey
  | none => .asWritten

/-- One exposed value before its own identity policy is attached. -/
public structure ExposedValue where
  typeName : String
  label : String
  fields : List (String × RelationalizerCore.Node IdentityKey IdentityKey) := []

/-- Attach a value's identity policy to its exposed structural payload. -/
@[expose] public def ExposedValue.withIdentity [ValueIdentity alpha]
    (typeKey : IdentityKey) (value : alpha) (node : ExposedValue) :
    RelationalizerCore.Node IdentityKey IdentityKey :=
  .value (valueIdentity typeKey value) node.typeName node.label node.fields

/-- A certified typed exposure into the structural nodes accepted by the shared engine.

Instances are generated automatically by `deriving SpytialReify` for supported datatypes. The laws
certify that field lookup is unambiguous and that the generic node interpretation implies the
independently generated reification checker. They do not certify the chosen identity policy;
`StructuralEncoding.Node.Coherent` is the separate condition for unchecked reconstruction. -/
public class StructuralExposure (alpha : Type u) [SpytialReify alpha]
    [StructuralReification alpha] [ValueIdentity alpha] where
  typeKey : IdentityKey
  expose : alpha → ExposedValue
  wellFormed : ∀ value, StructuralEncoding.Node.WellFormed
    ((expose value).withIdentity typeKey value)
  structuralComplete : ∀ datum root fuel value,
    StructuralEncoding.Node.representsAt datum root fuel
        ((expose value).withIdentity typeKey value) = true →
      StructuralReification.representsAt datum root fuel value = true

namespace StructuralExposure

/-- Expose a typed value as the input consumed by the shared structural walk. -/
@[expose] public def nodeOf {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha]
    (value : alpha) : RelationalizerCore.Node IdentityKey IdentityKey :=
  (StructuralExposure.expose value).withIdentity
    (StructuralExposure.typeKey (alpha := alpha)) value

/-- A certified exposure has pairwise-distinct field relations at every node. -/
public theorem nodeOf_wellFormed {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (value : alpha) :
    StructuralEncoding.Node.WellFormed (nodeOf value) :=
  StructuralExposure.wellFormed value

/-- Generic node interpretation is sufficient for the type's independent checker. -/
public theorem representsAt_of_node {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] {datum : JsonDataInstance} {root : String} {fuel : Nat}
    {value : alpha}
    (represented : StructuralEncoding.Node.representsAt datum root fuel (nodeOf value) = true) :
    StructuralReification.representsAt datum root fuel value = true :=
  StructuralExposure.structuralComplete datum root fuel value represented

end StructuralExposure

namespace Structural

/-- Send a typed exposure through the shared walk using its ordinary identity policy. -/
@[expose] public def relationalizeCandidate {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha]
    (value : alpha) : RootedJsonDataInstance :=
  RelationalizerCore.walk (StructuralExposure.nodeOf value)

/-- Reconstruction through the unchecked identity-aware walk. The identity law concerns the
input structure alone: equal reuse keys must denote the same full constructor/field tree,
including occurrences below the root. No runtime representation check or fallback is used. -/
public theorem reify_relationalizeCandidate {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (value : alpha)
    (meaning : IdentityKey × IdentityKey → RelationalizerCore.Node IdentityKey IdentityKey)
    (sound : StructuralEncoding.Node.IdentitySound meaning (StructuralExposure.nodeOf value)) :
    reify (relationalizeCandidate value) = Except.ok value := by
  apply reify_of_structurallyRepresents
  unfold StructurallyRepresents structurallyRepresents relationalizeCandidate
  apply StructuralExposure.representsAt_of_node
  exact StructuralEncoding.walk_sharing_represents _ meaning
    (StructuralExposure.nodeOf_wellFormed value) sound

/-- The usual structural identity law suffices: any two reachable occurrences with the same
reuse key have equal constructor/field structure. The conclusion uses the unchecked walk. -/
public theorem reify_relationalizeCandidate_of_coherent {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (value : alpha)
    (coherent : StructuralEncoding.Node.Coherent (StructuralExposure.nodeOf value)) :
    reify (relationalizeCandidate value) = Except.ok value := by
  apply reify_of_structurallyRepresents
  unfold StructurallyRepresents structurallyRepresents relationalizeCandidate
  apply StructuralExposure.representsAt_of_node
  exact StructuralEncoding.walk_coherent_represents _
    (StructuralExposure.nodeOf_wellFormed value) coherent

/-- Send the same exposure through the same walk with occurrence-preserving identity. -/
@[expose] public def relationalizeAsWritten {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha]
    (value : alpha) : RootedJsonDataInstance :=
  RelationalizerCore.walk
    (StructuralEncoding.Node.asWritten (StructuralExposure.nodeOf value))

/-- Occurrence-preserving traversal represents every certified typed exposure. No identity
classifier, runtime representation check, or fallback is needed for this theorem. -/
public theorem relationalizeAsWritten_represents {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (value : alpha) :
    StructurallyRepresents (relationalizeAsWritten value) value := by
  unfold StructurallyRepresents structurallyRepresents relationalizeAsWritten
  apply StructuralExposure.representsAt_of_node
  exact StructuralEncoding.walk_asWritten_represents
    (StructuralExposure.nodeOf value) (StructuralExposure.nodeOf_wellFormed value)

/-- Universal round trip for occurrence-preserving traversal of supported typed values. -/
@[simp] public theorem reify_relationalizeAsWritten {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (value : alpha) :
    reify (relationalizeAsWritten value) = Except.ok value :=
  reify_of_structurallyRepresents (relationalizeAsWritten_represents value)

/-- Relationalize a typed value by exposing it to the shared structural walk.

The identity-aware result is retained whenever the independent reification checker accepts it.
Otherwise the same exposure is walked occurrence-by-occurrence, preventing a lossy custom identity
from erasing constructor fields needed for reconstruction. -/
@[expose] public def relationalize {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha]
    (value : alpha) : RootedJsonDataInstance :=
  let candidate := relationalizeCandidate value
  if StructurallyRepresents candidate value then candidate else relationalizeAsWritten value

/-- Walking a certified typed exposure structurally represents its input. -/
public theorem relationalize_represents {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha]
    (value : alpha) : StructurallyRepresents (relationalize value) value := by
  by_cases represented : StructurallyRepresents (relationalizeCandidate value) value
  · change StructurallyRepresents
      (if StructurallyRepresents (relationalizeCandidate value) value then
        relationalizeCandidate value else relationalizeAsWritten value) value
    rw [if_pos represented]
    exact represented
  · change StructurallyRepresents
      (if StructurallyRepresents (relationalizeCandidate value) value then
        relationalizeCandidate value else relationalizeAsWritten value) value
    rw [if_neg represented]
    exact relationalizeAsWritten_represents value

/-- Universal round trip for every type with certified structural exposure. -/
@[simp] public theorem reify_relationalize {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha]
    (value : alpha) : reify (relationalize value) = Except.ok value :=
  reify_of_structurallyRepresents (relationalize_represents value)

end Structural

@[expose] public def natTypeKey : IdentityKey :=
  IdentityKey.ofString "Lean.Nat"

public instance [ValueIdentity Nat] : StructuralExposure Nat where
  typeKey := natTypeKey
  expose value := { typeName := "Nat", label := value.repr }
  wellFormed _ := by
    simp [ExposedValue.withIdentity, StructuralEncoding.Node.WellFormed,
      StructuralEncoding.Node.FieldsWellFormed]
  structuralComplete datum root fuel value represented := by
    change natRepresentsAt datum root fuel value = true
    cases fuel with
    | zero => simp [StructuralEncoding.Node.representsAt, ExposedValue.withIdentity] at represented
    | succ fuel =>
        cases atom : datum.expectAtom root "Nat" with
        | error error =>
            simp [StructuralEncoding.Node.representsAt, ExposedValue.withIdentity,
              JsonDataInstance.constructorRepresents, atom] at represented
        | ok found =>
            simp only [StructuralEncoding.Node.representsAt, ExposedValue.withIdentity,
              JsonDataInstance.constructorRepresents, atom, List.all_nil, Bool.and_true,
              beq_iff_eq] at represented
            simp [natRepresentsAt, atom, represented, parseNatLabel?_repr]

@[expose] public def stringTypeKey : IdentityKey :=
  IdentityKey.ofString "Lean.String"

public instance [ValueIdentity String] : StructuralExposure String where
  typeKey := stringTypeKey
  expose value := { typeName := "String", label := "\"" ++ value ++ "\"" }
  wellFormed _ := by
    simp [ExposedValue.withIdentity, StructuralEncoding.Node.WellFormed,
      StructuralEncoding.Node.FieldsWellFormed]
  structuralComplete datum root fuel value represented := by
    change stringRepresentsAt datum root fuel value = true
    cases fuel with
    | zero => simp [StructuralEncoding.Node.representsAt, ExposedValue.withIdentity] at represented
    | succ fuel =>
        cases atom : datum.expectAtom root "String" with
        | error error =>
            simp [StructuralEncoding.Node.representsAt, ExposedValue.withIdentity,
              JsonDataInstance.constructorRepresents, atom] at represented
        | ok found =>
            simpa [stringRepresentsAt, StructuralEncoding.Node.representsAt,
              ExposedValue.withIdentity, JsonDataInstance.constructorRepresents,
              atom] using represented

/-- Every primitive Nat survives the unchecked shared walk, for any selected identity policy. -/
public theorem Structural.reify_relationalizeCandidate_nat [ValueIdentity Nat] (value : Nat) :
    reify (relationalizeCandidate value) = Except.ok value :=
  reify_relationalizeCandidate_of_coherent value (StructuralEncoding.Node.coherent_leaf _ _ _)

/-- Every primitive String survives the unchecked shared walk, for any selected identity policy. -/
public theorem Structural.reify_relationalizeCandidate_string
    [ValueIdentity String] (value : String) :
    reify (relationalizeCandidate value) = Except.ok value :=
  reify_relationalizeCandidate_of_coherent value (StructuralEncoding.Node.coherent_leaf _ _ _)

end SpytialLean

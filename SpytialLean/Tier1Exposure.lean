module

public import SpytialLean.Identity
public import SpytialLean.RelationalizerCore
public import SpytialLean.ReifyCore
public import SpytialLean.Tier1Structural
public import SpytialLean.Tier1Sharing

namespace SpytialLean

/-!
# Typed exposure for the shared relationalization engine

`RelationalizerCore.Engine` is the graph-building state machine. It owns atom allocation, identity
interning, and relation construction. A `Tier1Exposure α` does not relationalize values or build a
`JsonDataInstance`; it only exposes an `α` as the structural nodes consumed by that walker.

The expression adapter in `Relationalizer` discovers the same information from `Lean.Expr` in
`MetaM`. For a supported datatype, `deriving SpytialReify` instead generates an ordinary pattern
matcher from `α` to structural nodes. The generated function is pure; only the deriving handler
that writes it requires `MetaM`.

The typed entry point is consequently just composition with the shared walker:

```text
α --Tier1Exposure.expose--> Node --RelationalizerCore.walk--> rooted datum
```

`reify_relationalizeCandidate_of_coherent` proves that this unchecked composition round-trips when
reuse keys reflect constructor/field structure at every reachable occurrence. This is an input
identity law, not an assumption that the output datum already represents the value. The shared
engine's preservation proof establishes that intermediate fact.

The optional `deriving Tier1Lossless` handler proves this identity hypothesis automatically for
concrete supported types. Its round-trip theorem applies to `relationalizeCandidate` below, not
to the checked convenience wrapper.

The convenience function `Tier1.relationalize` first keeps the normal identity-aware result when
that result structurally represents the input.
If a custom identity merges structurally different values, it sends the same exposed nodes through
the same walker with occurrence-preserving identity. This yields the universal round trip:

```lean
reify (Tier1.relationalize x) = Except.ok x
```

Tier 1 is the fragment for which exposure can currently be derived: primitives plus regular,
first-order, non-indexed inductive types and structures. Constructor data fields are explicit and
have distinct Spytial relation names within each constructor. Dependent or indexed families,
mutual, nested, and non-regular recursion, and proof-, type-, or function-valued fields remain out
of scope.
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

Instances are generated automatically by `deriving SpytialReify` for the Tier 1 fragment. The
laws certify that field lookup is unambiguous and that the generic node interpretation implies the
independently generated reification checker. They do not certify the chosen identity policy;
`Tier1Structural.Node.Coherent` is the separate hypothesis for unchecked shared reconstruction. -/
public class Tier1Exposure (alpha : Type u) [SpytialReify alpha]
    [Tier1Reification alpha] [ValueIdentity alpha] where
  typeKey : IdentityKey
  expose : alpha → ExposedValue
  wellFormed : ∀ value, Tier1Structural.Node.WellFormed
    ((expose value).withIdentity typeKey value)
  structuralComplete : ∀ datum root fuel value,
    Tier1Structural.Node.representsAt datum root fuel
        ((expose value).withIdentity typeKey value) = true →
      Tier1Reification.representsAt datum root fuel value = true

namespace Tier1Exposure

/-- Expose a typed value as the input consumed by the shared structural walk. -/
@[expose] public def nodeOf {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha]
    (value : alpha) : RelationalizerCore.Node IdentityKey IdentityKey :=
  (Tier1Exposure.expose value).withIdentity
    (Tier1Exposure.typeKey (alpha := alpha)) value

/-- A registered Tier 1 exposure has pairwise-distinct field relations at every node. -/
public theorem nodeOf_wellFormed {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] (value : alpha) :
    Tier1Structural.Node.WellFormed (nodeOf value) :=
  Tier1Exposure.wellFormed value

/-- Generic node interpretation is sufficient for the type's independent checker. -/
public theorem representsAt_of_node {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] {datum : JsonDataInstance} {root : String} {fuel : Nat}
    {value : alpha}
    (represented : Tier1Structural.Node.representsAt datum root fuel (nodeOf value) = true) :
    Tier1Reification.representsAt datum root fuel value = true :=
  Tier1Exposure.structuralComplete datum root fuel value represented

end Tier1Exposure

namespace Tier1

/-- Send a typed exposure through the shared walk using its ordinary identity policy. -/
@[expose] public def relationalizeCandidate {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha]
    (value : alpha) : RootedJsonDataInstance :=
  RelationalizerCore.walk (Tier1Exposure.nodeOf value)

/-- Reconstruction through the unchecked identity-aware walk. The identity law concerns the
input structure alone: equal reuse keys must denote the same full constructor/field tree,
including occurrences below the root. No runtime representation check or fallback is used. -/
public theorem reify_relationalizeCandidate {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] (value : alpha)
    (meaning : IdentityKey × IdentityKey → RelationalizerCore.Node IdentityKey IdentityKey)
    (sound : Tier1Structural.Node.IdentitySound meaning (Tier1Exposure.nodeOf value)) :
    reify (relationalizeCandidate value) = Except.ok value := by
  apply reify_of_tier1Represents
  unfold Tier1Represents tier1Represents relationalizeCandidate
  apply Tier1Exposure.representsAt_of_node
  exact Tier1Structural.walk_sharing_represents _ meaning
    (Tier1Exposure.nodeOf_wellFormed value) sound

/-- The usual structural identity law suffices: any two reachable occurrences with the same
reuse key have equal constructor/field structure. The conclusion uses the unchecked walk. -/
public theorem reify_relationalizeCandidate_of_coherent {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] (value : alpha)
    (coherent : Tier1Structural.Node.Coherent (Tier1Exposure.nodeOf value)) :
    reify (relationalizeCandidate value) = Except.ok value := by
  apply reify_of_tier1Represents
  unfold Tier1Represents tier1Represents relationalizeCandidate
  apply Tier1Exposure.representsAt_of_node
  exact Tier1Structural.walk_coherent_represents _
    (Tier1Exposure.nodeOf_wellFormed value) coherent

/-- Send the same exposure through the same walk with occurrence-preserving identity. -/
@[expose] public def relationalizeAsWritten {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha]
    (value : alpha) : RootedJsonDataInstance :=
  RelationalizerCore.walk
    (Tier1Structural.Node.asWritten (Tier1Exposure.nodeOf value))

/-- Occurrence-preserving traversal represents every certified typed exposure. No identity
classifier, runtime representation check, or fallback is needed for this theorem. -/
public theorem relationalizeAsWritten_represents {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] (value : alpha) :
    Tier1Represents (relationalizeAsWritten value) value := by
  unfold Tier1Represents tier1Represents relationalizeAsWritten
  apply Tier1Exposure.representsAt_of_node
  exact Tier1Structural.walk_asWritten_represents
    (Tier1Exposure.nodeOf value) (Tier1Exposure.nodeOf_wellFormed value)

/-- Universal round trip for occurrence-preserving traversal of supported typed values. -/
@[simp] public theorem reify_relationalizeAsWritten {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha] (value : alpha) :
    reify (relationalizeAsWritten value) = Except.ok value :=
  reify_of_tier1Represents (relationalizeAsWritten_represents value)

/-- Relationalize a typed value by exposing it to the shared structural walk.

The identity-aware result is retained whenever the independent reification checker accepts it.
Otherwise the same exposure is walked occurrence-by-occurrence, preventing a lossy custom identity
from erasing constructor fields needed for reconstruction. -/
@[expose] public def relationalize {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha]
    (value : alpha) : RootedJsonDataInstance :=
  let candidate := relationalizeCandidate value
  if Tier1Represents candidate value then candidate else relationalizeAsWritten value

/-- Walking a certified typed exposure structurally represents its input. -/
public theorem relationalize_represents {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha]
    (value : alpha) : Tier1Represents (relationalize value) value := by
  by_cases represented : Tier1Represents (relationalizeCandidate value) value
  · change Tier1Represents
      (if Tier1Represents (relationalizeCandidate value) value then
        relationalizeCandidate value else relationalizeAsWritten value) value
    rw [if_pos represented]
    exact represented
  · change Tier1Represents
      (if Tier1Represents (relationalizeCandidate value) value then
        relationalizeCandidate value else relationalizeAsWritten value) value
    rw [if_neg represented]
    exact relationalizeAsWritten_represents value

/-- Universal round trip for every type with certified Tier 1 exposure. -/
@[simp] public theorem reify_relationalize {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [ValueIdentity alpha]
    [Tier1Exposure alpha]
    (value : alpha) : reify (relationalize value) = Except.ok value :=
  reify_of_tier1Represents (relationalize_represents value)

end Tier1

@[expose] public def natTypeKey : IdentityKey :=
  IdentityKey.ofString "Lean.Nat"

public instance [ValueIdentity Nat] : Tier1Exposure Nat where
  typeKey := natTypeKey
  expose value := { typeName := "Nat", label := value.repr }
  wellFormed _ := by
    simp [ExposedValue.withIdentity, Tier1Structural.Node.WellFormed,
      Tier1Structural.Node.FieldsWellFormed]
  structuralComplete datum root fuel value represented := by
    change natRepresentsAt datum root fuel value = true
    cases fuel with
    | zero => simp [Tier1Structural.Node.representsAt, ExposedValue.withIdentity] at represented
    | succ fuel =>
        cases atom : datum.expectAtom root "Nat" with
        | error error =>
            simp [Tier1Structural.Node.representsAt, ExposedValue.withIdentity,
              JsonDataInstance.constructorRepresents, atom] at represented
        | ok found =>
            simp only [Tier1Structural.Node.representsAt, ExposedValue.withIdentity,
              JsonDataInstance.constructorRepresents, atom, List.all_nil, Bool.and_true,
              beq_iff_eq] at represented
            simp [natRepresentsAt, atom, represented, parseNatLabel?_repr]

@[expose] public def stringTypeKey : IdentityKey :=
  IdentityKey.ofString "Lean.String"

public instance [ValueIdentity String] : Tier1Exposure String where
  typeKey := stringTypeKey
  expose value := { typeName := "String", label := "\"" ++ value ++ "\"" }
  wellFormed _ := by
    simp [ExposedValue.withIdentity, Tier1Structural.Node.WellFormed,
      Tier1Structural.Node.FieldsWellFormed]
  structuralComplete datum root fuel value represented := by
    change stringRepresentsAt datum root fuel value = true
    cases fuel with
    | zero => simp [Tier1Structural.Node.representsAt, ExposedValue.withIdentity] at represented
    | succ fuel =>
        cases atom : datum.expectAtom root "String" with
        | error error =>
            simp [Tier1Structural.Node.representsAt, ExposedValue.withIdentity,
              JsonDataInstance.constructorRepresents, atom] at represented
        | ok found =>
            simpa [stringRepresentsAt, Tier1Structural.Node.representsAt,
              ExposedValue.withIdentity, JsonDataInstance.constructorRepresents,
              atom] using represented

/-- Every primitive Nat survives the unchecked shared walk, for any selected identity policy. -/
public theorem Tier1.reify_relationalizeCandidate_nat [ValueIdentity Nat] (value : Nat) :
    reify (relationalizeCandidate value) = Except.ok value :=
  reify_relationalizeCandidate_of_coherent value (Tier1Structural.Node.coherent_leaf _ _ _)

/-- Every primitive String survives the unchecked shared walk, for any selected identity policy. -/
public theorem Tier1.reify_relationalizeCandidate_string [ValueIdentity String] (value : String) :
    reify (relationalizeCandidate value) = Except.ok value :=
  reify_relationalizeCandidate_of_coherent value (Tier1Structural.Node.coherent_leaf _ _ _)

end SpytialLean

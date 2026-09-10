module

public import SpytialLean.Identity
public import SpytialLean.RelationalizerCore
public import SpytialLean.ReifyCore
public import SpytialLean.Tier1Structural

namespace SpytialLean

/-!
# Typed Tier 1 relationalization

A `Tier1Relationalizer α` describes a value as structural nodes consumed by the shared
`RelationalizerCore.Engine`. It does not construct a `JsonDataInstance` itself. Its laws certify
that the description has unambiguous field relations and that its generic structural
interpretation implies the independently generated `Tier1Reification` checker. Consequently,
every certified frontend satisfies:

```lean
reify (Tier1.relationalize x) = Except.ok x
```

The framework first runs the ordinary identity-aware engine. If its independently checked result
does not represent the input (which can happen when a custom identity merges structurally
different values), it reruns the same engine with occurrence-preserving identity. Thus safe sharing
is retained, but an arbitrary user identity cannot invalidate reconstruction. When no
`SpytialIdentity` is declared, a `ToIdentityKey` encoding supplies the default structural key;
types with neither policy are emitted occurrence-by-occurrence.
Classifier-backed identities are honored directly. An equivalence-only identity has no reusable
runtime key in this frontend and is therefore treated occurrence-by-occurrence.

The intended Tier 1 boundary is primitives plus regular, first-order, non-indexed inductive types
and structures. Constructor data fields are explicit and have distinct Spytial relation names;
proof-, type-, and function-valued fields, dependent or indexed families, mutual recursion,
nested recursion, and non-regular recursion remain outside this frontend. This module establishes
the shared engine, the typed interface, certified primitive instances, and the universal theorem.
`deriving Tier1Relationalizer` supplies these laws for the supported inductive fragment.
-/

/-- The pure fragment of identity needed by the structural relationalization engine. -/
public class Tier1Identity (alpha : Type u) where
  key? : alpha → Option IdentityKey

/-- An explicit Spytial identity declaration takes precedence, including `asWritten`. -/
public instance (priority := high) [SpytialIdentity alpha] : Tier1Identity alpha where
  key? value := SpytialIdentity.runtimeKey? value

/-- A primitive or container encoding supplies the default structural identity. -/
public instance (priority := low) [ToIdentityKey alpha] : Tier1Identity alpha where
  key? value := some (ToIdentityKey.toKey value)

/-- Types without a declared or encoded identity remain reconstructible occurrence-by-occurrence. -/
public instance (priority := 1) : Tier1Identity alpha where
  key? _ := none

/-- Convert the typed identity policy into the request understood by the shared engine. -/
@[expose] public def tier1Identity [Tier1Identity alpha] (typeKey : IdentityKey) (value : alpha) :
    RelationalizerCore.Identity IdentityKey IdentityKey :=
  match Tier1Identity.key? value with
  | some valueKey => .keyed typeKey valueKey
  | none => .asWritten

/-- The structural payload supplied by a typed frontend before identity is attached. -/
public structure Tier1Node where
  typeName : String
  label : String
  fields : List (String × RelationalizerCore.Node IdentityKey IdentityKey) := []

/-- Attach the type's identity policy to a structural payload. -/
@[expose] public def Tier1Node.withIdentity [Tier1Identity alpha]
    (typeKey : IdentityKey) (value : alpha) (node : Tier1Node) :
    RelationalizerCore.Node IdentityKey IdentityKey :=
  .value (tier1Identity typeKey value) node.typeName node.label node.fields

/-- A typed frontend whose structural descriptions are certified for the graph reifier. -/
public class Tier1Relationalizer (alpha : Type u) [SpytialReify alpha]
    [Tier1Reification alpha] [Tier1Identity alpha] where
  typeKey : IdentityKey
  describe : alpha → Tier1Node
  wellFormed : ∀ value, Tier1Structural.Node.WellFormed
    ((describe value).withIdentity typeKey value)
  structuralComplete : ∀ datum root fuel value,
    Tier1Structural.Node.representsAt datum root fuel
        ((describe value).withIdentity typeKey value) = true →
      Tier1Reification.representsAt datum root fuel value = true

namespace Tier1Relationalizer

/-- Invoke the structural frontend registered for a type. -/
@[expose] public def nodeOf {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
    (value : alpha) : RelationalizerCore.Node IdentityKey IdentityKey :=
  (Tier1Relationalizer.describe value).withIdentity
    (Tier1Relationalizer.typeKey (alpha := alpha)) value

/-- A registered Tier 1 description has pairwise-distinct field relations at every node. -/
public theorem nodeOf_wellFormed {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha] (value : alpha) :
    Tier1Structural.Node.WellFormed (nodeOf value) :=
  Tier1Relationalizer.wellFormed value

/-- The generic node interpretation is sufficient for the type's independent checker. -/
public theorem representsAt_of_node {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha] {datum : JsonDataInstance} {root : String} {fuel : Nat}
    {value : alpha}
    (represented : Tier1Structural.Node.representsAt datum root fuel (nodeOf value) = true) :
    Tier1Reification.representsAt datum root fuel value = true :=
  Tier1Relationalizer.structuralComplete datum root fuel value represented

end Tier1Relationalizer

namespace Tier1

/-- The ordinary identity-aware candidate emitted by the shared relationalization engine. -/
@[expose] public def relationalizeCandidate {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
    (value : alpha) : RootedJsonDataInstance :=
  RelationalizerCore.relationalize (Tier1Relationalizer.nodeOf value)

/-- The occurrence-preserving fallback, still emitted by the same relationalization engine. -/
@[expose] public def relationalizeAsWritten {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
    (value : alpha) : RootedJsonDataInstance :=
  RelationalizerCore.relationalize
    (Tier1Structural.Node.asWritten (Tier1Relationalizer.nodeOf value))

/-- Pure typed relationalization through the same identity-aware engine used by the meta adapter.

The normal identity-aware result is retained whenever the independent reification checker accepts
it. Otherwise the same structural description is emitted occurrence-by-occurrence, preventing a
lossy custom identity from erasing constructor fields needed for reconstruction. -/
@[expose] public def relationalize {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
    (value : alpha) : RootedJsonDataInstance :=
  let candidate := relationalizeCandidate value
  if Tier1Represents candidate value then candidate else relationalizeAsWritten value

/-- Typed Tier 1 relationalization structurally represents its input. -/
public theorem relationalize_represents {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
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
    unfold Tier1Represents tier1Represents relationalizeAsWritten
    apply Tier1Relationalizer.representsAt_of_node
    exact Tier1Structural.relationalize_asWritten_represents
      (Tier1Relationalizer.nodeOf value) (Tier1Relationalizer.nodeOf_wellFormed value)

/-- Universal round trip for every frontend certified as Tier 1. -/
@[simp] public theorem reify_relationalize {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
    (value : alpha) : reify (relationalize value) = Except.ok value :=
  reify_of_tier1Represents (relationalize_represents value)

end Tier1

@[expose] public def natTypeKey : IdentityKey :=
  IdentityKey.ofString "Lean.Nat"

public instance [Tier1Identity Nat] : Tier1Relationalizer Nat where
  typeKey := natTypeKey
  describe value := { typeName := "Nat", label := value.repr }
  wellFormed _ := by
    simp [Tier1Node.withIdentity, Tier1Structural.Node.WellFormed,
      Tier1Structural.Node.FieldsWellFormed]
  structuralComplete datum root fuel value represented := by
    change natRepresentsAt datum root fuel value = true
    cases fuel with
    | zero => simp [Tier1Structural.Node.representsAt, Tier1Node.withIdentity] at represented
    | succ fuel =>
        cases atom : datum.expectAtom root "Nat" with
        | error error =>
            simp [Tier1Structural.Node.representsAt, Tier1Node.withIdentity,
              JsonDataInstance.constructorRepresents, atom] at represented
        | ok found =>
            simp only [Tier1Structural.Node.representsAt, Tier1Node.withIdentity,
              JsonDataInstance.constructorRepresents, atom, List.all_nil, Bool.and_true,
              beq_iff_eq] at represented
            simp [natRepresentsAt, atom, represented, parseNatLabel?_repr]

@[expose] public def stringTypeKey : IdentityKey :=
  IdentityKey.ofString "Lean.String"

public instance [Tier1Identity String] : Tier1Relationalizer String where
  typeKey := stringTypeKey
  describe value := { typeName := "String", label := "\"" ++ value ++ "\"" }
  wellFormed _ := by
    simp [Tier1Node.withIdentity, Tier1Structural.Node.WellFormed,
      Tier1Structural.Node.FieldsWellFormed]
  structuralComplete datum root fuel value represented := by
    change stringRepresentsAt datum root fuel value = true
    cases fuel with
    | zero => simp [Tier1Structural.Node.representsAt, Tier1Node.withIdentity] at represented
    | succ fuel =>
        cases atom : datum.expectAtom root "String" with
        | error error =>
            simp [Tier1Structural.Node.representsAt, Tier1Node.withIdentity,
              JsonDataInstance.constructorRepresents, atom] at represented
        | ok found =>
            simpa [stringRepresentsAt, Tier1Structural.Node.representsAt,
              Tier1Node.withIdentity, JsonDataInstance.constructorRepresents,
              atom] using represented

end SpytialLean

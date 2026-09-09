module

public import SpytialLean.Identity
public import SpytialLean.RelationalizerCore
public import SpytialLean.ReifyCore

namespace SpytialLean

/-!
# Typed Tier 1 relationalization

A `Tier1Relationalizer α` describes a value as structural nodes consumed by the shared
`RelationalizerCore.Engine`. It does not construct a `JsonDataInstance` itself. Its law certifies,
against the independent `Tier1Represents` predicate, that the resulting graph contains enough
information to reconstruct the input. Consequently, every certified frontend satisfies:

```lean
reify (Tier1.relationalize x) = Except.ok x
```

The framework attaches the root node's identity. A classifier-backed `SpytialIdentity` supplies
its key; `asWritten` allocates occurrences separately. The typed frontend also treats an
equivalence-only identity conservatively as `asWritten`; the `MetaM` adapter retains its existing
evaluated equivalence-group behavior. When no `SpytialIdentity` is declared, a `ToIdentityKey`
encoding supplies the default structural key.

The intended Tier 1 boundary is primitives plus regular, first-order, non-indexed inductive types
and structures. Constructor data fields are explicit and have distinct Spytial relation names;
proof-, type-, and function-valued fields, dependent or indexed families, mutual recursion,
nested recursion, and non-regular recursion remain outside this frontend. This module establishes
the shared engine, the typed interface, and certified primitive instances. Automatic derivation
for the inductive fragment is separate work.
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
  represents : ∀ value, Tier1Represents
    (RelationalizerCore.relationalize ((describe value).withIdentity typeKey value)) value

namespace Tier1Relationalizer

/-- Invoke the structural frontend registered for a type. -/
@[expose] public def nodeOf {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
    (value : alpha) : RelationalizerCore.Node IdentityKey IdentityKey :=
  (Tier1Relationalizer.describe value).withIdentity
    (Tier1Relationalizer.typeKey (alpha := alpha)) value

end Tier1Relationalizer

namespace Tier1

/-- Pure typed relationalization through the same identity-aware engine used by the meta adapter. -/
@[expose] public def relationalize {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
    (value : alpha) : RootedJsonDataInstance :=
  RelationalizerCore.relationalize (Tier1Relationalizer.nodeOf value)

/-- Typed Tier 1 relationalization structurally represents its input. -/
public theorem relationalize_represents {alpha : Type u}
    [SpytialReify alpha] [Tier1Reification alpha] [Tier1Identity alpha]
    [Tier1Relationalizer alpha]
    (value : alpha) : Tier1Represents (relationalize value) value := by
  simpa [relationalize, Tier1Relationalizer.nodeOf] using
    Tier1Relationalizer.represents value

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
  represents value := by
    cases identity : Tier1Identity.key? value
    all_goals
      unfold Tier1Represents tier1Represents
      change natRepresentsAt _ _ _ _ = true
      simp [RelationalizerCore.relationalize, RelationalizerCore.Engine.addNode,
        RelationalizerCore.Engine.intern, RelationalizerCore.Engine.find?,
        RelationalizerCore.Engine.empty, RelationalizerCore.Graph.freshId,
        RelationalizerCore.Graph.addAtom, RelationalizerCore.Engine.addFields,
        RelationalizerCore.Graph.toDataInstance, Tier1Node.withIdentity, tier1Identity,
        identity, natRepresentsAt, JsonDataInstance.expectAtom, JsonDataInstance.atom,
        parseNatLabel?_repr, Bind.bind, Pure.pure, Except.bind, Except.pure]

@[expose] public def stringTypeKey : IdentityKey :=
  IdentityKey.ofString "Lean.String"

public instance [Tier1Identity String] : Tier1Relationalizer String where
  typeKey := stringTypeKey
  describe value := { typeName := "String", label := "\"" ++ value ++ "\"" }
  represents value := by
    cases identity : Tier1Identity.key? value
    all_goals
      unfold Tier1Represents tier1Represents
      change stringRepresentsAt _ _ _ _ = true
      simp [RelationalizerCore.relationalize, RelationalizerCore.Engine.addNode,
        RelationalizerCore.Engine.intern, RelationalizerCore.Engine.find?,
        RelationalizerCore.Engine.empty, RelationalizerCore.Graph.freshId,
        RelationalizerCore.Graph.addAtom, RelationalizerCore.Engine.addFields,
        RelationalizerCore.Graph.toDataInstance, Tier1Node.withIdentity, tier1Identity,
        identity, stringRepresentsAt, JsonDataInstance.expectAtom, JsonDataInstance.atom,
        Bind.bind, Pure.pure, Except.bind, Except.pure]

end SpytialLean

module

public import SpytialLean.LosslessIdentity

namespace SpytialLean

/-!
# Reconstruction ignores relation presentation

The structural view of a datum consists of its atoms and the tuples selected by structural field
IDs. Relation names, relation-level type metadata, and unrelated relation IDs are outside this
view. The round-trip theorem therefore survives any change preserving that view and the root.

The concrete operations below keep atoms fixed: they rename relations or append relations whose
IDs cannot denote structural fields. They impose no uniqueness condition on display names.
-/

namespace JsonDataInstance

/-- Equality of the data used for structural reconstruction. This compares atoms and keyed field
tuples directly; it does not assume anything about the output of a reifier or checker. -/
public structure SameStructure (left right : JsonDataInstance) : Prop where
  atoms : left.atoms = right.atoms
  fields : ∀ ownerType field, left.fieldTuples ownerType field = right.fieldTuples ownerType field

namespace SameStructure

public theorem refl (datum : JsonDataInstance) : datum.SameStructure datum :=
  ⟨rfl, fun _ _ => rfl⟩

public theorem symm {left right : JsonDataInstance} (same : left.SameStructure right) :
    right.SameStructure left :=
  ⟨same.atoms.symm, fun type field => (same.fields type field).symm⟩

public theorem trans {first second third : JsonDataInstance}
    (left : first.SameStructure second) (right : second.SameStructure third) :
    first.SameStructure third :=
  ⟨left.atoms.trans right.atoms, fun type field =>
    (left.fields type field).trans (right.fields type field)⟩

public theorem atom {left right : JsonDataInstance} (same : left.SameStructure right)
    (id : String) : left.atom id = right.atom id := by
  simp only [JsonDataInstance.atom, same.atoms]

public theorem child {left right : JsonDataInstance} (same : left.SameStructure right)
    (owner field : String) : left.child owner field = right.child owner field := by
  simp only [JsonDataInstance.child, same.atom, same.fields]

public theorem constructorRepresents {left right : JsonDataInstance}
    (same : left.SameStructure right) (root type label : String) (fields : Bool) :
    left.constructorRepresents root type label fields =
      right.constructorRepresents root type label fields := by
  simp only [JsonDataInstance.constructorRepresents, expectAtom, same.atom]

/-- Display names may be changed arbitrarily, including making every name identical. -/
public theorem renameRelations (datum : JsonDataInstance) (name : JsonRelation → String) :
    datum.SameStructure
      { datum with relations := datum.relations.map fun relation =>
        { relation with name := name relation } } := by
  constructor
  · rfl
  · intro type field
    simp only [fieldTuples, Array.toList_map, List.filter_map, List.flatMap_map]
    rfl

/-- Additional relations cannot affect reconstruction when their IDs are outside the structural
field namespace. Their display names, arities, metadata, and tuples are unrestricted. -/
public theorem appendRelations (datum : JsonDataInstance) (extra : Array JsonRelation)
    (disjoint : ∀ relation ∈ extra.toList, ∀ type field,
      relation.id ≠ fieldRelationId type field) :
    datum.SameStructure { datum with relations := datum.relations ++ extra } := by
  constructor
  · rfl
  · intro type field
    have noFields : extra.toList.filter
        (fun relation => relation.id == fieldRelationId type field) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro relation member
      simpa using disjoint relation member type field
    simp [fieldTuples, noFields]

end SameStructure
end JsonDataInstance

namespace StructuralEncoding.Node

/-- Generic structural interpretation factors through atoms and field IDs, independently of
relation names and all other relation records. -/
public theorem representsAt_congr {left right : JsonDataInstance}
    (same : left.SameStructure right) (root : String) (fuel : Nat)
    (node : RelationalizerCore.Node typeKey valueKey) :
    representsAt left root fuel node = representsAt right root fuel node := by
  induction fuel generalizing root node with
  | zero => simp only [representsAt]
  | succ fuel ih =>
      cases node with
      | value identity type label fields =>
          simp only [representsAt, same.constructorRepresents]
          congr 1
          apply List.all_congr rfl
          intro (name, child)
          simp only [JsonDataInstance.childRepresentsWith, same.child, ih]

end StructuralEncoding.Node

namespace Structural

/-- The unchecked round trip is stable under any change preserving the structural view and root.
The hypotheses concern the input identity policy and raw graph content, never decoder success. -/
public theorem reify_relationalizeCandidate_of_sameStructure {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] (value : alpha)
    (coherent : StructuralEncoding.Node.Coherent (StructuralExposure.nodeOf value))
    (datum : RootedJsonDataInstance)
    (root : datum.root = (relationalizeCandidate value).root)
    (same : (relationalizeCandidate value).data.SameStructure datum.data) :
    reify datum = Except.ok value := by
  apply reify_of_structurallyRepresents
  apply StructuralExposure.representsAt_of_node
  rw [root, ← same.atoms, ← StructuralEncoding.Node.representsAt_congr same]
  exact StructuralEncoding.walk_coherent_represents _
    (StructuralExposure.nodeOf_wellFormed value) coherent

/-- For certified lossless types, presentation changes need only preserve the structural view
and root. Display-name uniqueness is not a hypothesis. -/
public theorem reify_relationalize_of_sameStructure {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] [LosslessIdentity alpha] (value : alpha)
    (datum : RootedJsonDataInstance)
    (root : datum.root = (relationalizeCandidate value).root)
    (same : (relationalizeCandidate value).data.SameStructure datum.data) :
    reify datum = Except.ok value :=
  reify_relationalizeCandidate_of_sameStructure value
    (LosslessIdentity.coherent value) datum root same

/-- Renaming relations preserves the unchecked round trip for every certified lossless value. -/
public theorem reify_relationalize_renameRelations {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] [LosslessIdentity alpha] (value : alpha)
    (name : JsonRelation → String) :
    let datum := relationalizeCandidate value
    reify { datum with data.relations := datum.data.relations.map fun relation =>
      { relation with name := name relation } } = Except.ok value := by
  apply reify_relationalize_of_sameStructure value
  · rfl
  · exact JsonDataInstance.SameStructure.renameRelations _ name

/-- Adding relations with nonstructural IDs preserves the unchecked round trip, even when their
display names coincide with field names. Atoms and the root remain fixed. -/
public theorem reify_relationalize_appendRelations {alpha : Type u}
    [SpytialReify alpha] [StructuralReification alpha] [ValueIdentity alpha]
    [StructuralExposure alpha] [LosslessIdentity alpha] (value : alpha) (extra : Array JsonRelation)
    (disjoint : ∀ relation ∈ extra.toList, ∀ type field,
      relation.id ≠ fieldRelationId type field) :
    let datum := relationalizeCandidate value
    reify { datum with data.relations := datum.data.relations ++ extra } = Except.ok value := by
  apply reify_relationalize_of_sameStructure value
  · rfl
  · exact JsonDataInstance.SameStructure.appendRelations _ extra disjoint

end Structural
end SpytialLean

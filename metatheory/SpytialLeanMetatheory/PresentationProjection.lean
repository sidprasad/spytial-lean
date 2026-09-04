module

public import SpytialLeanMetatheory.ProductionTraceInstance

public section

/-!
# Projection to Spytial display relations

Semantic relation symbols retain their Lean head and hidden parameters.
Spytial intentionally uses the shorter relation name as a display key. A
display relation is the union of every tuple with that name.

The rows remain typed individually. Different semantic relations may have
different column types or arities without corrupting one another. This is the
ragged relation model used by Spytial: the relation-level type list is only a
summary, while each tuple carries its own schema.
-/

namespace SpytialLean.Metatheory

universe u v

/-- One tuple after semantic relation identity has been replaced by its
    Spytial display name. Its schema remains attached to the tuple. -/
public structure PresentedTuple {SemanticType : Type u}
    (Entry : SemanticType → Type v) where
  relation : String
  columns : List SemanticType
  entries : TypedTuple Entry columns

namespace PresentedTuple

/-- Forget tuple shape while retaining the type of every displayed atom. -/
@[expose] public def atoms {SemanticType : Type u} {Entry : SemanticType → Type v}
    (tuple : PresentedTuple Entry) : List (TypedAtom Entry) :=
  tuple.entries.atoms

end PresentedTuple

/-- A typed tuple always has one atom occurrence for each schema column. -/
public theorem typedTuple_atoms_length {SemanticType : Type u}
    {Entry : SemanticType → Type v} {types : List SemanticType}
    (tuple : TypedTuple Entry types) : tuple.atoms.length = types.length := by
  induction tuple with
  | nil => rfl
  | cons head tail ih =>
      simpa only [TypedTuple.atoms, List.length_cons] using congrArg Nat.succ ih

/-- Presentation cannot create a malformed tuple: column alignment follows
    from the intrinsic type of its entries. -/
public theorem PresentedTuple.columns_aligned {SemanticType : Type u}
    {Entry : SemanticType → Type v} (tuple : PresentedTuple Entry) :
    tuple.atoms.length = tuple.columns.length :=
  typedTuple_atoms_length tuple.entries

/-- Replace a semantic relation symbol by a display name while retaining the
    tuple-local schema and entries. -/
@[expose] public def presentTuple {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (displayName : signature.Relation → String)
    (tuple : RelationalTuple signature Entry) : PresentedTuple Entry where
  relation := displayName tuple.relation
  columns := signature.columns tuple.relation
  entries := tuple.entries

/-- Project a semantic tuple list to the flat rows consumed by display
    relation grouping. -/
@[expose] public def presentTuples {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (displayName : signature.Relation → String)
    (tuples : List (RelationalTuple signature Entry)) :
    List (PresentedTuple Entry) :=
  tuples.map (presentTuple displayName)

/-- Projection neither drops nor invents rows. -/
public theorem mem_presentTuples_iff {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (displayName : signature.Relation → String)
    (tuples : List (RelationalTuple signature Entry)) (displayed : PresentedTuple Entry) :
    displayed ∈ presentTuples displayName tuples ↔
      ∃ source ∈ tuples, presentTuple displayName source = displayed := by
  simp [presentTuples]

/-- Projecting a union is the union of the two projections. -/
public theorem presentTuples_append {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (displayName : signature.Relation → String)
    (left right : List (RelationalTuple signature Entry)) :
    presentTuples displayName (left ++ right) =
      presentTuples displayName left ++ presentTuples displayName right := by
  simp [presentTuples]

/-- At the level of relational membership, list append is ordinary set union. -/
public theorem mem_presentTuples_append_iff {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (displayName : signature.Relation → String)
    (left right : List (RelationalTuple signature Entry))
    (row : PresentedTuple Entry) :
    row ∈ presentTuples displayName (left ++ right) ↔
      row ∈ presentTuples displayName left ∨
        row ∈ presentTuples displayName right := by
  simp [presentTuples]

/-- Select the rows that Spytial sees under one relation name. -/
@[expose] public def rowsNamed {SemanticType : Type u}
    {Entry : SemanticType → Type v} (relation : String)
    (rows : List (PresentedTuple Entry)) : List (PresentedTuple Entry) :=
  rows.filter fun row => row.relation == relation

/-- A row belongs to a named display relation exactly when it has that name. -/
public theorem mem_rowsNamed_iff {SemanticType : Type u}
    {Entry : SemanticType → Type v} (relation : String)
    (rows : List (PresentedTuple Entry)) (row : PresentedTuple Entry) :
    row ∈ rowsNamed relation rows ↔ row ∈ rows ∧ row.relation = relation := by
  simp [rowsNamed]

/-- Grouping by a display name preserves union. -/
public theorem rowsNamed_append {SemanticType : Type u}
    {Entry : SemanticType → Type v} (relation : String)
    (left right : List (PresentedTuple Entry)) :
    rowsNamed relation (left ++ right) =
      rowsNamed relation left ++ rowsNamed relation right := by
  simp [rowsNamed]

/-- Same-name semantic relations coalesce at presentation, independently of
    their internal heads and parameters. -/
public theorem same_name_coalesces {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (displayName : signature.Relation → String)
    (left right : RelationalTuple signature Entry)
    (sameName : displayName left.relation = displayName right.relation) :
    (presentTuple displayName left).relation =
      (presentTuple displayName right).relation :=
  sameName

/-- Coalescing relation names does not coalesce tuple schemas. -/
public theorem presentTuple_preserves_schema {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (displayName : signature.Relation → String)
    (tuple : RelationalTuple signature Entry) :
    (presentTuple displayName tuple).columns = signature.columns tuple.relation :=
  rfl

/-- Even when two same-name relations have different schemas, presentation
    retains that difference on their individual rows. -/
public theorem same_name_keeps_distinct_schemas {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (displayName : signature.Relation → String)
    (left right : RelationalTuple signature Entry)
    (sameName : displayName left.relation = displayName right.relation)
    (differentSchemas : signature.columns left.relation ≠
      signature.columns right.relation) :
    (presentTuple displayName left).relation =
        (presentTuple displayName right).relation ∧
      (presentTuple displayName left).columns ≠
        (presentTuple displayName right).columns :=
  ⟨sameName, differentSchemas⟩

/-- The short name exposed to Spytial for an expression-backed relation. -/
@[expose] public def leanRelationDisplayName {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (relation : meaning.signature.Relation) : String :=
  (exprRelation relation).name

namespace Inspection

/-- The display rows obtained from both checked sources of an inspection. -/
@[expose] public def presentation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (inspection : Inspection meaning) :
    List (PresentedTuple (LeanExprMeaning.ExprAtom meaning)) :=
  presentTuples leanRelationDisplayName
    (inspection.structuralTuples ++ inspection.provedTuples)

/-- Computation and proof contribute by ordinary union to the same display
    relation namespace. -/
public theorem presentation_union {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (inspection : Inspection meaning) :
    inspection.presentation =
      presentTuples leanRelationDisplayName inspection.structuralTuples ++
        presentTuples leanRelationDisplayName inspection.provedTuples := by
  simp [presentation, presentTuples]

/-- For each Spytial relation name, its rows are exactly the union of the
    computed rows and proof-derived rows with that name. -/
public theorem named_presentation_union {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (inspection : Inspection meaning)
    (relation : String) :
    rowsNamed relation inspection.presentation =
      rowsNamed relation
          (presentTuples leanRelationDisplayName inspection.structuralTuples) ++
        rowsNamed relation
          (presentTuples leanRelationDisplayName inspection.provedTuples) := by
  rw [presentation_union, rowsNamed_append]

end Inspection

namespace CheckedCoreTrace

/-- Presentation rows obtained directly from a checked built-in trace. -/
@[expose] public def presentation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : SpytialLean.TracedDataInstance} (checked : CheckedCoreTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    List (PresentedTuple (LeanExprMeaning.ExprAtom meaning)) :=
  (checked.inspection evidence).presentation

/-- Combined checked-trace result: the semantic inspection is sound and its
    display relation at each name is precisely the union of computation and
    proof. -/
public theorem sound_and_presentation_union {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : SpytialLean.TracedDataInstance} (checked : CheckedCoreTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    Completes context (checked.inspection evidence).data
        (ProductionTupleHolds.ground meaning) ∧
      ∀ relation,
        rowsNamed relation (checked.presentation evidence) =
          rowsNamed relation
              (presentTuples leanRelationDisplayName
                (structuralTraceTuples checked.structural evidence)) ++
            rowsNamed relation
              (presentTuples leanRelationDisplayName
                (proofTraceTuples checked.proofs evidence)) := by
  refine ⟨checked.inspection_sound evidence, ?_⟩
  intro relation
  simpa [CheckedCoreTrace.presentation, CheckedCoreTrace.inspection] using
    Inspection.named_presentation_union (checked.inspection evidence) relation

end CheckedCoreTrace

end SpytialLean.Metatheory

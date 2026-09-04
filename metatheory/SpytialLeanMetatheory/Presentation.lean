module

public import SpytialLeanMetatheory.Inspection

public section

/-!
# Projection to the Spytial interface

Semantic relation symbols may contain more information than their displayed
Spytial names. Projection keeps every row's typed schema. Several semantic
relations may therefore share one display name without becoming one semantic
relation. Projection neither adds nor removes rows.
-/

namespace SpytialLean.Metatheory

universe u v w x

/-- The part of a typed atom consumed by the presentation layer. -/
public structure PresentedAtom (SemanticType : Type u) where
  id : String
  type : SemanticType

/-- One row after relation symbols have been projected to Spytial names. -/
public structure PresentedTuple (SemanticType : Type u) where
  relation : String
  columns : List SemanticType
  atoms : List String

/-- The typed positive interface supplied to a Spytial specification. -/
public structure PresentedData (SemanticType : Type u) where
  atoms : List (PresentedAtom SemanticType)
  tuples : List (PresentedTuple SemanticType)

namespace TypedTuple

/-- Project the identifiers from a typed tuple. -/
@[expose] public def ids {SemanticType : Type u}
    {Entry : SemanticType → Type v}
    (id : ∀ {type}, Entry type → String) :
    {types : List SemanticType} → TypedTuple Entry types → List String
  | _, .nil => []
  | _, .cons head tail => id head :: ids id tail

end TypedTuple

/-- Project one semantic atom to its identifier and semantic type. -/
@[expose] public def presentAtom {SemanticType : Type u}
    {Entry : SemanticType → Type v}
    (id : ∀ {type}, Entry type → String) : TypedAtom Entry → PresentedAtom SemanticType
  | ⟨type, value⟩ => { id := id value, type }

/-- Project one semantic tuple to a named, typed Spytial row. -/
@[expose] public def presentTuple {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (id : ∀ {type}, Entry type → String)
    (tuple : RelationalTuple signature Entry) : PresentedTuple SemanticType where
  relation := signature.name tuple.relation
  columns := signature.columns tuple.relation
  atoms := tuple.entries.ids id

/-- Project semantic relational data to the interface consumed by Spytial. -/
@[expose] public def present {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (id : ∀ {type}, Entry type → String)
    (data : RelationalData signature Entry) : PresentedData SemanticType where
  atoms := data.atoms.map (presentAtom id)
  tuples := data.tuples.map (presentTuple id)

/-- Projection preserves positive union exactly. Rows from semantic relations
    with one display name therefore appear together while retaining their
    individual schemas. -/
public theorem present_union {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (id : ∀ {type}, Entry type → String)
    (left right : RelationalData signature Entry) :
    present id (left.union right) = {
      atoms := (present id left).atoms ++ (present id right).atoms
      tuples := (present id left).tuples ++ (present id right).tuples
    } := by
  simp [present, RelationalData.union, List.map_append]

/-- Any Spytial specification applied to structural data is insensitive to
    whether computation or proof supplied the resolved value. -/
public theorem same_spytial_specification_for_computation_and_proof
    {World : Type u} {SemanticType : Type v} {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    (relationalizer : StructuralRelationalizer context Value signature Entry interpretation)
    (id : ∀ {type}, Entry type → String)
    {expression : ContextualValue context Value}
    (computed : ComputationResult expression)
    (proved : ProofResult expression)
    (specification : PresentedData SemanticType → Prop) :
    specification (present id (relationalizer.relationalize computed.value)) ↔
      specification (present id (relationalizer.relationalize proved.value)) := by
  rw [computation_and_proof_have_same_relational_structure
    relationalizer computed proved]

end SpytialLean.Metatheory

module

public import IykykMetatheory

public section

/-!
# Typed positive relational data

This file defines the common interface between Lean inspection and Spytial.
An instance contains typed atoms and positive tuples. Its meaning is deliberately
one-sided: every tuple that is present must be true, while an absent tuple says
nothing.

The definitions do not mention `Lean.Expr` or the implementation of Lean's
kernel. They describe the semantic object produced by relational inspection.
-/

namespace SpytialLean.Metatheory

universe u v w x

/-- An entry packaged together with its semantic type. -/
public structure TypedAtom {SemanticType : Type u}
    (Entry : SemanticType → Type v) where
  type : SemanticType
  value : Entry type

/-- A heterogeneous tuple indexed by its column types. -/
public inductive TypedTuple {SemanticType : Type u}
    (Entry : SemanticType → Type v) : List SemanticType → Type (max u v) where
  | nil : TypedTuple Entry []
  | cons {type types} :
      Entry type → TypedTuple Entry types → TypedTuple Entry (type :: types)

namespace TypedTuple

/-- Apply a type-preserving map to every entry of a typed tuple. -/
@[expose] public def map {SemanticType : Type u}
    {Source : SemanticType → Type v} {Target : SemanticType → Type w}
    (transform : ∀ {type}, Source type → Target type) :
    {types : List SemanticType} → TypedTuple Source types → TypedTuple Target types
  | _, .nil => .nil
  | _, .cons head tail => .cons (transform head) (map transform tail)

/-- Forget tuple shape while retaining the type of every entry. -/
@[expose] public def atoms {SemanticType : Type u}
    {Entry : SemanticType → Type v} :
    {types : List SemanticType} → TypedTuple Entry types → List (TypedAtom Entry)
  | _, .nil => []
  | _, .cons (type := type) head tail =>
      { type, value := head } :: atoms tail

end TypedTuple

/-- A relation symbol includes its typed columns and its Spytial display name. -/
public structure RelationalSignature (SemanticType : Type u) where
  Relation : Type v
  columns : Relation → List SemanticType
  name : Relation → String

/-- One intrinsically typed relational tuple. -/
public structure RelationalTuple {SemanticType : Type u}
    (signature : RelationalSignature SemanticType)
    (Entry : SemanticType → Type v) where
  relation : signature.Relation
  entries : TypedTuple Entry (signature.columns relation)

namespace RelationalTuple

/-- The typed atoms used by a tuple. -/
@[expose] public def atoms {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (tuple : RelationalTuple signature Entry) : List (TypedAtom Entry) :=
  tuple.entries.atoms

/-- Map a tuple without changing its relation or column types. -/
@[expose] public def map {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Source : SemanticType → Type v} {Target : SemanticType → Type w}
    (transform : ∀ {type}, Source type → Target type)
    (tuple : RelationalTuple signature Source) : RelationalTuple signature Target where
  relation := tuple.relation
  entries := tuple.entries.map transform

end RelationalTuple

/-- Finite positive relational data over one common atom representation. -/
public structure RelationalData {SemanticType : Type u}
    (signature : RelationalSignature SemanticType)
    (Entry : SemanticType → Type v) where
  atoms : List (TypedAtom Entry)
  tuples : List (RelationalTuple signature Entry)
  tuples_use_known_atoms : ∀ tuple, tuple ∈ tuples → ∀ atom, atom ∈ tuple.atoms →
    atom ∈ atoms

namespace RelationalData

/-- Build data from a tuple list, using exactly the atoms mentioned by it. -/
@[expose] public def ofTuples {SemanticType : Type u}
    (signature : RelationalSignature SemanticType)
    (Entry : SemanticType → Type v)
    (tuples : List (RelationalTuple signature Entry)) : RelationalData signature Entry where
  atoms := tuples.flatMap (·.atoms)
  tuples
  tuples_use_known_atoms := by
    intro tuple tuplePresent atom atomPresent
    induction tuples with
    | nil => contradiction
    | cons head tail ih =>
        cases tuplePresent with
        | head _ => exact List.mem_append_left _ atomPresent
        | tail _ tuplePresent =>
            exact List.mem_append_right _ (ih tuplePresent)

/-- The empty positive instance. -/
public def empty {SemanticType : Type u}
    (signature : RelationalSignature SemanticType)
    (Entry : SemanticType → Type v) : RelationalData signature Entry where
  atoms := []
  tuples := []
  tuples_use_known_atoms := by simp

/-- Positive union. It preserves the provenance split by using list append. -/
@[expose] public def union {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (left right : RelationalData signature Entry) : RelationalData signature Entry where
  atoms := left.atoms ++ right.atoms
  tuples := left.tuples ++ right.tuples
  tuples_use_known_atoms := by
    intro tuple tuplePresent atom atomPresent
    rcases List.mem_append.mp tuplePresent with leftPresent | rightPresent
    · exact List.mem_append_left _
        (left.tuples_use_known_atoms tuple leftPresent atom atomPresent)
    · exact List.mem_append_right _
        (right.tuples_use_known_atoms tuple rightPresent atom atomPresent)

/-- `large` contains every positive atom and tuple in `small`. -/
public structure ContainedIn {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (small large : RelationalData signature Entry) : Prop where
  atoms : ∀ atom, atom ∈ small.atoms → atom ∈ large.atoms
  tuples : ∀ tuple, tuple ∈ small.tuples → tuple ∈ large.tuples

/-- A union contains its left input. -/
public theorem containedIn_union_left {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (left right : RelationalData signature Entry) :
    ContainedIn left (left.union right) where
  atoms _ present := List.mem_append_left _ present
  tuples _ present := List.mem_append_left _ present

/-- A union contains its right input. -/
public theorem containedIn_union_right {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v}
    (left right : RelationalData signature Entry) :
    ContainedIn right (left.union right) where
  atoms _ present := List.mem_append_right _ present
  tuples _ present := List.mem_append_right _ present

end RelationalData

/-- A ground model interprets every type and relation in each possible world. -/
public structure RelationalModel (World : Type u) {SemanticType : Type v}
    (signature : RelationalSignature SemanticType) where
  Carrier : SemanticType → Type w
  holds : (world : World) → (relation : signature.Relation) →
    TypedTuple Carrier (signature.columns relation) → Prop

/-- Meaning for the atoms used by a finite relational instance. -/
public structure AtomInterpretation {World : Type u} {SemanticType : Type v}
    (context : Iykyk.Metatheory.Context World)
    {signature : RelationalSignature SemanticType}
    (model : RelationalModel World signature)
    (Entry : SemanticType → Type x) where
  denote : ∀ {type}, Entry type → ∀ world, context world → model.Carrier type

/-- Interpret one tuple in one world compatible with the proof context. -/
@[expose] public def tupleHolds {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    (interpretation : AtomInterpretation context model Entry)
    (tuple : RelationalTuple signature Entry)
    (world : World) (compatible : context world) : Prop :=
  model.holds world tuple.relation
    (tuple.entries.map fun atom => interpretation.denote atom world compatible)

/-- The possible-world fact asserted by one positive tuple. -/
@[expose] public def tupleFact {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    (interpretation : AtomInterpretation context model Entry)
    (tuple : RelationalTuple signature Entry) : Iykyk.Metatheory.Fact World :=
  fun world => ∀ compatible : context world,
    tupleHolds interpretation tuple world compatible

/-- Every reported tuple is true in every world compatible with the context. -/
@[expose] public def Sound {World : Type u} {SemanticType : Type v}
    (context : Iykyk.Metatheory.Context World)
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    (interpretation : AtomInterpretation context model Entry)
    (data : RelationalData signature Entry) : Prop :=
  ∀ world (compatible : context world) tuple, tuple ∈ data.tuples →
    tupleHolds interpretation tuple world compatible

/-- Soundness is equivalently entailment of every reported tuple fact. -/
public theorem sound_iff_tuple_facts {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {data : RelationalData signature Entry} :
    Sound context interpretation data ↔
      ∀ tuple ∈ data.tuples,
        Iykyk.Metatheory.Entails context (tupleFact interpretation tuple) := by
  constructor
  · intro sound tuple present world compatible _
    exact sound world compatible tuple present
  · intro entailed world compatible tuple present
    exact entailed tuple present world compatible compatible

/-- Combining two sound positive instances preserves soundness. -/
public theorem sound_union {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {left right : RelationalData signature Entry}
    (leftSound : Sound context interpretation left)
    (rightSound : Sound context interpretation right) :
    Sound context interpretation (left.union right) := by
  intro world compatible tuple present
  rcases List.mem_append.mp present with leftPresent | rightPresent
  · exact leftSound world compatible tuple leftPresent
  · exact rightSound world compatible tuple rightPresent

/-- Removing positive information cannot make a sound instance unsound. -/
public theorem sound_of_containedIn {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {small large : RelationalData signature Entry}
    (contained : RelationalData.ContainedIn small large)
    (largeSound : Sound context interpretation large) :
    Sound context interpretation small := by
  intro world compatible tuple present
  exact largeSound world compatible tuple (contained.tuples tuple present)

/-- The empty positive instance is sound in every relational model. -/
public theorem sound_empty {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    (interpretation : AtomInterpretation context model Entry) :
    Sound context interpretation (RelationalData.empty signature Entry) := by
  simp [Sound, RelationalData.empty]

end SpytialLean.Metatheory

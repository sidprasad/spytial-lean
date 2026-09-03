module

public import IykykMetatheory

public section

/-!
# Semantic relational instances

This module gives the common semantic target for computation- and
proof-derived relationalization. Types, relation symbols, and their column
types are intrinsic: an ill-typed tuple cannot be constructed. Atoms denote
values in every possible world compatible with the IYKYK context.

The model is deliberately independent of `Lean.Expr`. Connecting Lean terms
to `SemanticType` and `Carrier` is part of the trusted reflection boundary;
the definitions below state what that bridge must preserve.
-/

namespace SpytialLean.Metatheory

universe u v w x

/-- An existentially packaged entry retaining its semantic type index. -/
public structure TypedAtom {SemanticType : Type u}
    (Entry : SemanticType → Type v) where
  type : SemanticType
  value : Entry type

/-- A heterogeneous tuple indexed by its list of semantic column types. -/
public inductive TypedTuple {SemanticType : Type u}
    (Entry : SemanticType → Type v) : List SemanticType → Type (max u v) where
  | nil : TypedTuple Entry []
  | cons {type types} :
      Entry type → TypedTuple Entry types → TypedTuple Entry (type :: types)

namespace TypedTuple

/-- Apply a type-preserving function to every entry of a typed tuple. -/
@[expose] public def map {SemanticType : Type u} {Source : SemanticType → Type v}
    {Target : SemanticType → Type w} (transform : ∀ {type}, Source type → Target type) :
    {types : List SemanticType} → TypedTuple Source types → TypedTuple Target types
  | _, .nil => .nil
  | _, .cons head tail =>
      .cons (transform head) (map (Source := Source) (Target := Target) transform tail)

/-- Forget tuple shape while retaining each entry's semantic type. -/
@[expose] public def atoms {SemanticType : Type u} {Entry : SemanticType → Type v} :
    {types : List SemanticType} → TypedTuple Entry types → List (TypedAtom Entry)
  | _, .nil => []
  | _, .cons (type := type) head tail =>
      { type, value := head } :: atoms tail

end TypedTuple

/-- A typed relational signature. The column types belong to the relation
    symbol, rather than to presentation strings in the JSON wire format. -/
public structure RelationalSignature (SemanticType : Type u) where
  Relation : Type v
  columns : Relation → List SemanticType

/-- One intrinsically typed tuple under a relational signature. -/
public structure RelationalTuple {SemanticType : Type u}
    (signature : RelationalSignature SemanticType)
    (Entry : SemanticType → Type v) where
  relation : signature.Relation
  entries : TypedTuple Entry (signature.columns relation)

namespace RelationalTuple

/-- Apply a type-preserving map to all entries while retaining the relation. -/
@[expose] public def map {SemanticType : Type u} {signature : RelationalSignature SemanticType}
    {Source : SemanticType → Type v} {Target : SemanticType → Type w}
    (transform : ∀ {type}, Source type → Target type)
    (tuple : RelationalTuple signature Source) : RelationalTuple signature Target where
  relation := tuple.relation
  entries := tuple.entries.map transform

/-- The typed atoms occurring in a relational tuple. -/
@[expose] public def atoms {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v} (tuple : RelationalTuple signature Entry) :
    List (TypedAtom Entry) :=
  tuple.entries.atoms

end RelationalTuple

/-- A ground relational structure gives meaning to every typed relation tuple. -/
public structure GroundInstance {SemanticType : Type u}
    (signature : RelationalSignature SemanticType)
    (Carrier : SemanticType → Type w) where
  holds : (relation : signature.Relation) →
    TypedTuple Carrier (signature.columns relation) → Prop

/-- A finite positive relational instance. Its atoms may depend on a proof
    that the current world is compatible with the IYKYK context. Computed
    atoms simply ignore that proof; proof-extracted witnesses may use it. -/
public structure SemanticInstance {World : Type u} {SemanticType : Type v}
    (context : Iykyk.Metatheory.Context World)
    (signature : RelationalSignature SemanticType)
    (Carrier : SemanticType → Type w) where
  Atom : SemanticType → Type x
  denote : ∀ {type}, Atom type → ∀ world, context world → Carrier type
  atoms : List (TypedAtom Atom)
  tuples : List (RelationalTuple signature Atom)
  tuplesUseKnownAtoms : ∀ tuple, tuple ∈ tuples → ∀ atom, atom ∈ tuple.atoms →
    atom ∈ atoms

namespace SemanticInstance

/-- Interpret all atoms of a tuple in one compatible world. -/
@[expose] public def denoteTuple {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (data : SemanticInstance context signature Carrier) (world : World)
    (compatible : context world) (tuple : RelationalTuple signature data.Atom) :
    RelationalTuple signature Carrier :=
  tuple.map fun atom => data.denote atom world compatible

/-- The proposition asserted by one emitted tuple at one compatible world. -/
@[expose] public def TupleHolds {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (data : SemanticInstance context signature Carrier)
    (ground : World → GroundInstance signature Carrier)
    (tuple : RelationalTuple signature data.Atom) (world : World)
    (compatible : context world) : Prop :=
  let denoted := data.denoteTuple world compatible tuple
  (ground world).holds denoted.relation denoted.entries

/-- Turn a tuple into an IYKYK semantic fact. Outside the context it makes no
    claim; inside the context it must hold for the tuple's denotation. -/
@[expose] public def tupleFact {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (data : SemanticInstance context signature Carrier)
    (ground : World → GroundInstance signature Carrier)
    (tuple : RelationalTuple signature data.Atom) :
    Iykyk.Metatheory.Fact World :=
  fun world => ∀ compatible : context world,
    data.TupleHolds ground tuple world compatible

end SemanticInstance

/-- Every positive tuple in the partial instance is true in every compatible
    possible world. No condition is imposed on tuples absent from the instance. -/
@[expose] public def Completes {World : Type u} {SemanticType : Type v}
    (context : Iykyk.Metatheory.Context World)
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (data : SemanticInstance context signature Carrier)
    (ground : World → GroundInstance signature Carrier) : Prop :=
  ∀ world (compatible : context world) tuple, tuple ∈ data.tuples →
    data.TupleHolds ground tuple world compatible

/-- Completion is exactly IYKYK entailment of every emitted relational fact. -/
public theorem completes_iff_tupleFacts {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {data : SemanticInstance context signature Carrier}
    {ground : World → GroundInstance signature Carrier} :
    Completes context data ground ↔
      ∀ tuple ∈ data.tuples,
        Iykyk.Metatheory.Entails context (data.tupleFact ground tuple) := by
  constructor
  · intro completion tuple present
    simp only [Iykyk.Metatheory.Entails, SemanticInstance.tupleFact]
    intro world _ compatible
    exact completion world compatible tuple present
  · intro entailed
    simp only [Completes]
    intro world compatible tuple present
    have tupleEntailed := entailed tuple present
    simp only [Iykyk.Metatheory.Entails, SemanticInstance.tupleFact] at tupleEntailed
    exact tupleEntailed world compatible compatible

/-- The empty positive instance is completed by every possible world. -/
public theorem completes_empty {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {Atom : SemanticType → Type x}
    {denote : ∀ {type}, Atom type → ∀ world, context world → Carrier type}
    (ground : World → GroundInstance signature Carrier) :
    Completes context ({
      Atom := Atom
      denote := denote
      atoms := []
      tuples := []
      tuplesUseKnownAtoms := by simp
    } : SemanticInstance context signature Carrier) ground := by
  simp [Completes]

end SpytialLean.Metatheory

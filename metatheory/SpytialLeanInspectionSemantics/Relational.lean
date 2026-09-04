module

public import IykykMetatheory

public section

/-!
# Relational instances and their meaning

Inspection produces finite positive relational data. Its atoms are typed semantic terms: an atom
has a value in every world that satisfies the current Lean context. A tuple is well typed by
construction, and its meaning comes from the corresponding relation in a model.

An absent tuple says nothing. Soundness only requires every tuple that is present to hold.
-/

namespace SpytialLean.Semantics

universe u v w

/-- A typed relational vocabulary. -/
public structure Signature (Ty : Type u) where
  Relation : Type v
  columns : Relation → List Ty

/-- A heterogeneous list indexed by its entry types. -/
public inductive Arguments {Ty : Type u} (Entry : Ty → Type v) : List Ty → Type (max u v)
  where
  | nil : Arguments Entry []
  | cons {sort sorts} : Entry sort → Arguments Entry sorts → Arguments Entry (sort :: sorts)

namespace Arguments

/-- Apply a type-preserving function to every argument. -/
@[expose] public def map {Ty : Type u} {Source : Ty → Type v} {Target : Ty → Type w}
    (transform : ∀ {sort}, Source sort → Target sort) :
    {sorts : List Ty} → Arguments Source sorts → Arguments Target sorts
  | _, .nil => .nil
  | _, .cons head tail => .cons (transform head) (map transform tail)

end Arguments

/-- An atom packaged with its semantic type. -/
public structure TypedAtom {Ty : Type u} (Entry : Ty → Type v) where
  sort : Ty
  value : Entry sort

namespace Arguments

/-- Forget the tuple shape while retaining each atom's type. -/
@[expose] public def atoms {Ty : Type u} {Entry : Ty → Type v} :
    {sorts : List Ty} → Arguments Entry sorts → List (TypedAtom Entry)
  | _, .nil => []
  | _, .cons (sort := sort) head tail => ⟨sort, head⟩ :: atoms tail

end Arguments

/-- One tuple whose argument types are fixed by its relation symbol. -/
public structure Tuple {Ty : Type u} (signature : Signature Ty)
    (Entry : Ty → Type v) where
  relation : signature.Relation
  arguments : Arguments Entry (signature.columns relation)

namespace Tuple

/-- The typed atoms used by a tuple. -/
@[expose] public def atoms {Ty : Type u} {signature : Signature Ty}
    {Entry : Ty → Type v} (tuple : Tuple signature Entry) : List (TypedAtom Entry) :=
  tuple.arguments.atoms

end Tuple

/-- A possible-world interpretation of the relational vocabulary. -/
public structure Model (World : Type u) {Ty : Type v} (signature : Signature Ty) where
  Carrier : Ty → Type w
  holds : (world : World) → (relation : signature.Relation) →
    Arguments Carrier (signature.columns relation) → Prop

/-- A typed term interpreted in every world compatible with the current context. -/
public abbrev Atom {World : Type u} {Ty : Type v} (context : Iykyk.Metatheory.Context World)
    {signature : Signature Ty} (model : Model World signature) (sort : Ty) :=
  ∀ world, context world → model.Carrier sort

/-- A finite positive relational instance. Every tuple refers only to listed atoms. -/
public structure Instance {World : Type u} {Ty : Type v}
    (context : Iykyk.Metatheory.Context World) {signature : Signature Ty}
    (model : Model World signature) where
  atoms : List (TypedAtom (Atom context model))
  tuples : List (Tuple signature (Atom context model))
  tuplesUseAtoms : ∀ tuple, tuple ∈ tuples → ∀ atom, atom ∈ tuple.atoms → atom ∈ atoms

namespace Instance

/-- An instance containing one atom and no relational claims. -/
@[expose] public def ofAtom {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty} (atom : Atom context model sort) :
    Instance context model where
  atoms := [⟨sort, atom⟩]
  tuples := []
  tuplesUseAtoms := by simp

/-- An instance containing one tuple and exactly the atoms used by that tuple. -/
@[expose] public def ofTuple {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (tuple : Tuple signature (Atom context model)) :
    Instance context model where
  atoms := tuple.atoms
  tuples := [tuple]
  tuplesUseAtoms := by
    intro candidate present atom atomPresent
    simp only [List.mem_singleton] at present
    subst candidate
    exact atomPresent

/-- Combine independently obtained positive information. -/
@[expose] public def union {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (left right : Instance context model) :
    Instance context model where
  atoms := left.atoms ++ right.atoms
  tuples := left.tuples ++ right.tuples
  tuplesUseAtoms := by
    intro tuple present atom atomPresent
    rcases List.mem_append.mp present with fromLeft | fromRight
    · exact List.mem_append_left _ (left.tuplesUseAtoms tuple fromLeft atom atomPresent)
    · exact List.mem_append_right _ (right.tuplesUseAtoms tuple fromRight atom atomPresent)

/-- `larger` retains every atom and tuple reported by `smaller`. -/
public structure ContainedIn {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (smaller larger : Instance context model) : Prop where
  atoms : ∀ atom, atom ∈ smaller.atoms → atom ∈ larger.atoms
  tuples : ∀ tuple, tuple ∈ smaller.tuples → tuple ∈ larger.tuples

/-- Adding information by union retains the left instance. -/
public theorem containedIn_union_left {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (left right : Instance context model) :
    ContainedIn left (left.union right) where
  atoms _ present := List.mem_append_left _ present
  tuples _ present := List.mem_append_left _ present

end Instance

/-- The proposition denoted by a tuple in one compatible world. -/
@[expose] public def Tuple.Holds {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (tuple : Tuple signature (Atom context model))
    (world : World) (compatible : context world) : Prop :=
  model.holds world tuple.relation
    (tuple.arguments.map fun atom => atom world compatible)

/-- The possible-world fact represented by a tuple. -/
@[expose] public def Tuple.fact {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (tuple : Tuple signature (Atom context model)) :
    Iykyk.Metatheory.Fact World :=
  fun world => ∀ compatible : context world, tuple.Holds world compatible

/-- Every tuple reported by an instance is true in every world allowed by the context. -/
@[expose] public def Instance.Sound {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (data : Instance context model) : Prop :=
  ∀ tuple, tuple ∈ data.tuples → ∀ world (compatible : context world),
    tuple.Holds world compatible

/-- Combining sound positive instances preserves soundness. -/
public theorem Instance.sound_union {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {left right : Instance context model}
    (leftSound : left.Sound) (rightSound : right.Sound) : (left.union right).Sound := by
  intro tuple present world compatible
  rcases List.mem_append.mp present with fromLeft | fromRight
  · exact leftSound tuple fromLeft world compatible
  · exact rightSound tuple fromRight world compatible

/-- An atom alone makes no relational claim and is therefore sound. -/
public theorem Instance.sound_ofAtom {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty} (atom : Atom context model sort) :
    (Instance.ofAtom atom).Sound := by
  simp [Instance.Sound, Instance.ofAtom]

/-- A singleton tuple instance is sound exactly when its tuple holds. -/
public theorem Instance.sound_ofTuple {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (tuple : Tuple signature (Atom context model))
    (holds : ∀ world (compatible : context world), tuple.Holds world compatible) :
    (Instance.ofTuple tuple).Sound := by
  intro candidate present world compatible
  simp only [Instance.ofTuple, List.mem_singleton] at present
  subst candidate
  exact holds world compatible

end SpytialLean.Semantics

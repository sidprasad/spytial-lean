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

/-- A finite set presented extensionally. The list is only a finiteness certificate: membership is
the predicate, so an element has one identity even if a witness list happens to repeat it. -/
public structure FiniteSet (α : Type u) where
  contains : α → Prop
  finite : ∃ items : List α, ∀ item, contains item ↔ item ∈ items

instance {α : Type u} : Membership α (FiniteSet α) := ⟨FiniteSet.contains⟩

namespace FiniteSet

/-- Two finite sets are equal when they have the same members. -/
@[ext] public theorem ext {α : Type u} {left right : FiniteSet α}
    (same : ∀ item, item ∈ left ↔ item ∈ right) : left = right := by
  cases left with
  | mk leftContains leftFinite =>
    cases right with
    | mk rightContains rightFinite =>
      have containsEq : leftContains = rightContains :=
        funext fun item => propext (same item)
      subst rightContains
      rfl

/-- The empty finite set. -/
@[expose] public def empty {α : Type u} : FiniteSet α where
  contains := fun _ => False
  finite := ⟨[], by simp⟩

/-- A singleton finite set. -/
@[expose] public def singleton {α : Type u} (item : α) : FiniteSet α where
  contains := fun candidate => candidate = item
  finite := ⟨[item], by simp⟩

/-- The finite set represented by a list. Repeated list entries still denote one member. -/
@[expose] public def ofList {α : Type u} (items : List α) : FiniteSet α where
  contains := fun item => item ∈ items
  finite := ⟨items, by simp⟩

/-- Set union. Membership is disjunction, so union is deduplicating by definition. -/
@[expose] public def union {α : Type u} (left right : FiniteSet α) : FiniteSet α where
  contains := fun item => item ∈ left ∨ item ∈ right
  finite := by
    obtain ⟨leftItems, leftFinite⟩ := left.finite
    obtain ⟨rightItems, rightFinite⟩ := right.finite
    refine ⟨leftItems ++ rightItems, fun item => ?_⟩
    constructor
    · rintro (present | present)
      · exact List.mem_append_left _ ((leftFinite item).mp present)
      · exact List.mem_append_right _ ((rightFinite item).mp present)
    · intro present
      rcases List.mem_append.mp present with fromLeft | fromRight
      · exact Or.inl ((leftFinite item).mpr fromLeft)
      · exact Or.inr ((rightFinite item).mpr fromRight)

/-- Map a finite set through a function. -/
@[expose] public def image {α : Type u} {β : Type v} (transform : α → β)
    (source : FiniteSet α) : FiniteSet β where
  contains := fun target => ∃ item, item ∈ source ∧ transform item = target
  finite := by
    obtain ⟨items, sourceFinite⟩ := source.finite
    refine ⟨items.map transform, fun target => ?_⟩
    constructor
    · rintro ⟨item, present, rfl⟩
      exact List.mem_map.mpr ⟨item, (sourceFinite item).mp present, rfl⟩
    · intro present
      obtain ⟨item, itemPresent, rfl⟩ := List.mem_map.mp present
      exact ⟨item, (sourceFinite item).mpr itemPresent, rfl⟩

@[simp] public theorem mem_empty {α : Type u} (item : α) : item ∉ (empty : FiniteSet α) := by
  simp [Membership.mem, empty]

@[simp] public theorem mem_singleton {α : Type u} {item candidate : α} :
    candidate ∈ singleton item ↔ candidate = item := by
  rfl

@[simp] public theorem mem_ofList {α : Type u} {item : α} {items : List α} :
    item ∈ ofList items ↔ item ∈ items := by
  rfl

@[simp] public theorem mem_union {α : Type u} {item : α} {left right : FiniteSet α} :
    item ∈ left.union right ↔ item ∈ left ∨ item ∈ right := by
  rfl

@[simp] public theorem mem_image {α : Type u} {β : Type v} {target : β} {transform : α → β}
    {source : FiniteSet α} :
    target ∈ source.image transform ↔
      ∃ item, item ∈ source ∧ transform item = target := by
  rfl

public theorem union_self {α : Type u} (data : FiniteSet α) : data.union data = data := by
  apply ext
  intro item
  simp [mem_union]

end FiniteSet

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

/-- Concatenate two typed argument lists. -/
@[expose] public def append {Ty : Type u} {Entry : Ty → Type v} :
    {left right : List Ty} → Arguments Entry left → Arguments Entry right →
      Arguments Entry (left ++ right)
  | [], _, .nil, right => right
  | _ :: _, _, .cons head tail, right => .cons head (append tail right)

@[simp] public theorem map_append {Ty : Type u} {Source : Ty → Type v}
    {Target : Ty → Type w} (transform : ∀ {sort}, Source sort → Target sort) :
    ∀ {left right : List Ty} (first : Arguments Source left)
      (second : Arguments Source right),
      (first.append second).map transform =
        (first.map transform).append (second.map transform)
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ tail, second => by
      simp only [append, map, map_append transform tail second]

/-- Remove the final argument from a nonempty typed argument list. -/
@[expose] public def init {Ty : Type u} {Entry : Ty → Type v} {finalSort : Ty} :
    {sorts : List Ty} → Arguments Entry (sorts ++ [finalSort]) → Arguments Entry sorts
  | [], .cons _ .nil => .nil
  | _ :: _, .cons head tail => .cons head (init tail)

/-- Select the final argument from a nonempty typed argument list. -/
@[expose] public def last {Ty : Type u} {Entry : Ty → Type v} {finalSort : Ty} :
    {sorts : List Ty} → Arguments Entry (sorts ++ [finalSort]) → Entry finalSort
  | [], .cons result .nil => result
  | _ :: _, .cons _ tail => last tail

@[simp] public theorem init_append_singleton {Ty : Type u} {Entry : Ty → Type v}
    {finalSort : Ty} : ∀ {sorts : List Ty} (arguments : Arguments Entry sorts)
      (result : Entry finalSort),
      init (arguments.append (.cons result .nil)) = arguments
  | [], .nil, _ => rfl
  | _ :: _, .cons _ tail, result => by
      simp only [append, init, init_append_singleton tail result]

@[simp] public theorem last_append_singleton {Ty : Type u} {Entry : Ty → Type v}
    {finalSort : Ty} : ∀ {sorts : List Ty} (arguments : Arguments Entry sorts)
      (result : Entry finalSort),
      last (arguments.append (.cons result .nil)) = result
  | [], .nil, _ => rfl
  | _ :: _, .cons _ tail, result => by
      simp only [append, last, last_append_singleton tail result]

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

/-- A finite positive relational instance. Atoms and tuples are extensional finite sets, so union
cannot duplicate a semantic atom or relational row. Every tuple refers only to listed atoms. -/
public structure Instance {World : Type u} {Ty : Type v}
    (context : Iykyk.Metatheory.Context World) {signature : Signature Ty}
    (model : Model World signature) where
  atoms : FiniteSet (TypedAtom (Atom context model))
  tuples : FiniteSet (Tuple signature (Atom context model))
  tuplesUseAtoms : ∀ tuple, tuple ∈ tuples → ∀ atom, atom ∈ tuple.atoms → atom ∈ atoms

namespace Instance

/-- The instance with no atoms and no relational claims. -/
@[expose] public def empty {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} : Instance context model where
  atoms := FiniteSet.empty
  tuples := FiniteSet.empty
  tuplesUseAtoms := by
    intro tuple present
    exact False.elim present

/-- An instance containing one atom and no relational claims. -/
@[expose] public def ofAtom {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty} (atom : Atom context model sort) :
    Instance context model where
  atoms := FiniteSet.singleton ⟨sort, atom⟩
  tuples := FiniteSet.empty
  tuplesUseAtoms := by
    intro tuple present
    exact False.elim present

/-- An instance containing one tuple and exactly the atoms used by that tuple. -/
@[expose] public def ofTuple {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (tuple : Tuple signature (Atom context model)) :
    Instance context model where
  atoms := .ofList tuple.atoms
  tuples := .singleton tuple
  tuplesUseAtoms := by
    intro candidate present atom atomPresent
    simp only [FiniteSet.mem_singleton] at present
    subst candidate
    exact atomPresent

/-- Combine independently obtained positive information. -/
@[expose] public def union {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (left right : Instance context model) :
    Instance context model where
  atoms := left.atoms.union right.atoms
  tuples := left.tuples.union right.tuples
  tuplesUseAtoms := by
    intro tuple present atom atomPresent
    rcases present with fromLeft | fromRight
    · exact Or.inl (left.tuplesUseAtoms tuple fromLeft atom atomPresent)
    · exact Or.inr (right.tuplesUseAtoms tuple fromRight atom atomPresent)

/-- `larger` retains every atom and tuple reported by `smaller`. -/
public structure ContainedIn {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (smaller larger : Instance context model) : Prop where
  atoms : ∀ atom, atom ∈ smaller.atoms → atom ∈ larger.atoms
  tuples : ∀ tuple, tuple ∈ smaller.tuples → tuple ∈ larger.tuples

/-- Identity isomorphism for canonical semantic atoms: both instances contain the same typed
atoms and tuples. Runtime atom IDs are presentation names for these semantic atoms, so this is the
typed relational isomorphism relevant after origin erasure. -/
public structure TypedIsomorphic {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (left right : Instance context model) : Prop where
  forward : ContainedIn left right
  backward : ContainedIn right left

/-- Equality of canonical typed instances induces a typed relational isomorphism. -/
public theorem typedIsomorphic_of_eq {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {left right : Instance context model}
    (equal : left = right) : TypedIsomorphic left right := by
  subst right
  exact ⟨⟨fun _ present => present, fun _ present => present⟩,
    ⟨fun _ present => present, fun _ present => present⟩⟩

/-- Adding information by union retains the left instance. -/
public theorem containedIn_union_left {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (left right : Instance context model) :
    ContainedIn left (left.union right) where
  atoms _ present := Or.inl present
  tuples _ present := Or.inl present

/-- Combining an instance with itself is exactly idempotent, including its atom collection. -/
public theorem union_self {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (data : Instance context model) :
    data.union data = data := by
  cases data with
  | mk atoms tuples uses =>
    have atomsEq : atoms.union atoms = atoms := FiniteSet.union_self atoms
    have tuplesEq : tuples.union tuples = tuples := FiniteSet.union_self tuples
    simp only [union, atomsEq, tuplesEq]

/-- Encountering the same typed atom twice still allocates one semantic atom. -/
public theorem ofAtom_union_self {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty} (atom : Atom context model sort) :
    (ofAtom atom).union (ofAtom atom) = ofAtom atom :=
  union_self _

/-- Encountering the same typed tuple twice still emits one relational row. -/
public theorem ofTuple_union_self {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (tuple : Tuple signature (Atom context model)) :
    (ofTuple tuple).union (ofTuple tuple) = ofTuple tuple :=
  union_self _

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
  rcases present with fromLeft | fromRight
  · exact leftSound tuple fromLeft world compatible
  · exact rightSound tuple fromRight world compatible

/-- The empty instance makes no relational claim and is therefore sound. -/
public theorem Instance.sound_empty {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} :
    (Instance.empty (context := context) (model := model)).Sound := by
  intro tuple present
  exact False.elim present

/-- An atom alone makes no relational claim and is therefore sound. -/
public theorem Instance.sound_ofAtom {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty} (atom : Atom context model sort) :
    (Instance.ofAtom atom).Sound := by
  intro tuple present
  exact False.elim present

/-- A singleton tuple instance is sound exactly when its tuple holds. -/
public theorem Instance.sound_ofTuple {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} (tuple : Tuple signature (Atom context model))
    (holds : ∀ world (compatible : context world), tuple.Holds world compatible) :
    (Instance.ofTuple tuple).Sound := by
  intro candidate present world compatible
  simp only [Instance.ofTuple, FiniteSet.mem_singleton] at present
  subst candidate
  exact holds world compatible

end SpytialLean.Semantics

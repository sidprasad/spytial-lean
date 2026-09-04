module

public import SpytialLeanMetatheory.SemanticInstance

public section

/-!
# Agreement between relational descriptions

Computed and proof-derived relational descriptions should agree independently
of fresh atom identifiers and list order. The comparison is a bijection of
typed atoms that preserves their values and all positive tuples.
-/

namespace SpytialLean.Metatheory

universe u v w x y z

namespace TypedAtom

/-- Apply a type-preserving function to one existentially packaged atom. -/
@[expose] public def map {SemanticType : Type u} {Source : SemanticType → Type v}
    {Target : SemanticType → Type w}
    (transform : ∀ {type}, Source type → Target type) :
    TypedAtom Source → TypedAtom Target
  | ⟨type, value⟩ => ⟨type, transform value⟩

end TypedAtom

namespace TypedTuple

/-- Mapping a typed tuple twice is the same as mapping it by the composite. -/
public theorem map_map {SemanticType : Type u} {First : SemanticType → Type v}
    {Second : SemanticType → Type w} {Third : SemanticType → Type x}
    (right : ∀ {type}, Second type → Third type)
    (left : ∀ {type}, First type → Second type)
    {types : List SemanticType} (tuple : TypedTuple First types) :
    (tuple.map left).map right = tuple.map fun value => right (left value) := by
  induction tuple with
  | nil => rfl
  | cons head tail ih =>
      simp only [map]
      rw [ih]

/-- Pointwise equal maps give equal typed tuples. -/
public theorem map_congr {SemanticType : Type u} {Source : SemanticType → Type v}
    {Target : SemanticType → Type w}
    (left right : ∀ {type}, Source type → Target type)
    (equal : ∀ {type} (value : Source type), left value = right value)
    {types : List SemanticType} (tuple : TypedTuple Source types) :
    tuple.map left = tuple.map right := by
  induction tuple with
  | nil => rfl
  | cons head tail ih =>
      simp only [map]
      rw [equal head, ih]

/-- Mapping by the identity function changes no typed entry. -/
public theorem map_id {SemanticType : Type u} {Entry : SemanticType → Type v}
    {types : List SemanticType} (tuple : TypedTuple Entry types) :
    tuple.map (fun value => value) = tuple := by
  induction tuple with
  | nil => rfl
  | cons head tail ih =>
      simp only [map]
      rw [ih]

/-- Forgetting tuple shape after a map maps the corresponding packaged atom
    list. -/
public theorem atoms_map {SemanticType : Type u} {Source : SemanticType → Type v}
    {Target : SemanticType → Type w}
    (transform : ∀ {type}, Source type → Target type)
    {types : List SemanticType} (tuple : TypedTuple Source types) :
    (tuple.map transform).atoms = tuple.atoms.map (TypedAtom.map transform) := by
  induction tuple with
  | nil => rfl
  | cons head tail ih =>
      simp only [map, atoms, List.map_cons, TypedAtom.map]
      rw [ih]

end TypedTuple

namespace RelationalTuple

/-- Mapping a relational tuple twice composes the atom maps. -/
public theorem map_map {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {First : SemanticType → Type v} {Second : SemanticType → Type w}
    {Third : SemanticType → Type x}
    (right : ∀ {type}, Second type → Third type)
    (left : ∀ {type}, First type → Second type)
    (tuple : RelationalTuple signature First) :
    (tuple.map left).map right = tuple.map fun value => right (left value) := by
  rcases tuple with ⟨relation, entries⟩
  simp only [map]
  rw [TypedTuple.map_map]

/-- Mapping a relational tuple by the identity changes nothing. -/
public theorem map_id {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Entry : SemanticType → Type v} (tuple : RelationalTuple signature Entry) :
    tuple.map (fun value => value) = tuple := by
  rcases tuple with ⟨relation, entries⟩
  simp only [map]
  rw [TypedTuple.map_id]

/-- Pointwise equal atom maps give equal relational tuples. -/
public theorem map_congr {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Source : SemanticType → Type v} {Target : SemanticType → Type w}
    (left right : ∀ {type}, Source type → Target type)
    (equal : ∀ {type} (value : Source type), left value = right value)
    (tuple : RelationalTuple signature Source) :
    tuple.map left = tuple.map right := by
  rcases tuple with ⟨relation, entries⟩
  simp only [map]
  rw [TypedTuple.map_congr left right equal entries]

/-- Mapping a tuple forward and then backward is the identity when the atom
    maps are pointwise inverses. -/
public theorem map_leftInverse {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Source : SemanticType → Type v} {Target : SemanticType → Type w}
    (forward : ∀ {type}, Source type → Target type)
    (backward : ∀ {type}, Target type → Source type)
    (inverse : ∀ {type} (value : Source type), backward (forward value) = value)
    (tuple : RelationalTuple signature Source) :
    (tuple.map forward).map backward = tuple := by
  rw [map_map]
  calc
    tuple.map (fun value => backward (forward value)) =
        tuple.map (fun value => value) := map_congr _ _ inverse tuple
    _ = tuple := map_id tuple

/-- Packaged atoms of a mapped relational tuple are the mapped packaged atoms
    of the source tuple. -/
public theorem atoms_map {SemanticType : Type u}
    {signature : RelationalSignature SemanticType}
    {Source : SemanticType → Type v} {Target : SemanticType → Type w}
    (transform : ∀ {type}, Source type → Target type)
    (tuple : RelationalTuple signature Source) :
    (tuple.map transform).atoms = tuple.atoms.map (TypedAtom.map transform) := by
  rcases tuple with ⟨relation, entries⟩
  exact TypedTuple.atoms_map transform entries

end RelationalTuple

/-- A structure-preserving map between semantic instances. It preserves atom
    types and denotations and maps every positive atom and tuple to the target.
    It makes no claim that tuples missing from the source are false. -/
public structure SemanticHom {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (source : SemanticInstance.{u, v, w, x} context signature Carrier)
    (target : SemanticInstance.{u, v, w, y} context signature Carrier) where
  atom : ∀ {type}, source.Atom type → target.Atom type
  preserves_denotation : ∀ {type} (value : source.Atom type) world
    (compatible : context world),
    target.denote (atom value) world compatible = source.denote value world compatible
  maps_atoms : ∀ {type} (value : source.Atom type),
    ({ type := type, value } : TypedAtom source.Atom) ∈ source.atoms →
      ({ type := type, value := atom value } : TypedAtom target.Atom) ∈ target.atoms
  maps_tuples : ∀ tuple, tuple ∈ source.tuples →
    tuple.map (fun value => atom value) ∈ target.tuples

namespace SemanticHom

/-- Every semantic instance maps to itself. -/
public def refl {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (data : SemanticInstance.{u, v, w, x} context signature Carrier) :
    SemanticHom data data where
  atom := fun value => value
  preserves_denotation := by simp
  maps_atoms := by simp
  maps_tuples := by
    intro tuple present
    simpa only [RelationalTuple.map_id] using present

/-- Semantic homomorphisms compose. -/
public def comp {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {first : SemanticInstance.{u, v, w, x} context signature Carrier}
    {second : SemanticInstance.{u, v, w, y} context signature Carrier}
    {third : SemanticInstance.{u, v, w, z} context signature Carrier}
    (right : SemanticHom second third) (left : SemanticHom first second) :
    SemanticHom first third where
  atom := fun value => right.atom (left.atom value)
  preserves_denotation := by
    intro type value world compatible
    rw [right.preserves_denotation, left.preserves_denotation]
  maps_atoms := by
    intro type value present
    exact right.maps_atoms (left.atom value) (left.maps_atoms value present)
  maps_tuples := by
    intro tuple present
    have mapped := right.maps_tuples
      (tuple.map fun value => left.atom value) (left.maps_tuples tuple present)
    simpa only [RelationalTuple.map_map] using mapped

/-- A semantic homomorphism preserves the denotation of a whole tuple. -/
public theorem denoteTuple_mapped {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {source : SemanticInstance.{u, v, w, x} context signature Carrier}
    {target : SemanticInstance.{u, v, w, y} context signature Carrier}
    (hom : SemanticHom source target) (world : World) (compatible : context world)
    (tuple : RelationalTuple signature source.Atom) :
    target.denoteTuple world compatible
        (tuple.map fun value => hom.atom value) =
      source.denoteTuple world compatible tuple := by
  rcases tuple with ⟨relation, entries⟩
  simp only [SemanticInstance.denoteTuple, RelationalTuple.map]
  congr 1
  rw [TypedTuple.map_map]
  apply TypedTuple.map_congr
  intro type value
  exact hom.preserves_denotation value world compatible

/-- Consequently, a mapped tuple is true exactly when its source tuple is
    true. -/
public theorem tupleHolds_mapped_iff {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {source : SemanticInstance.{u, v, w, x} context signature Carrier}
    {target : SemanticInstance.{u, v, w, y} context signature Carrier}
    (hom : SemanticHom source target) (ground : World → GroundInstance signature Carrier)
    (tuple : RelationalTuple signature source.Atom) (world : World)
    (compatible : context world) :
    target.TupleHolds ground (tuple.map fun value => hom.atom value) world compatible ↔
      source.TupleHolds ground tuple world compatible := by
  simp only [SemanticInstance.TupleHolds]
  rw [hom.denoteTuple_mapped]

/-- If the target satisfies every tuple and contains the image of the source,
    then it also satisfies every source tuple. -/
public theorem completes_source {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {source : SemanticInstance.{u, v, w, x} context signature Carrier}
    {target : SemanticInstance.{u, v, w, y} context signature Carrier}
    (hom : SemanticHom source target) (ground : World → GroundInstance signature Carrier)
    (targetComplete : Completes context target ground) : Completes context source ground := by
  intro world compatible tuple present
  have mappedHolds := targetComplete world compatible
    (tuple.map fun value => hom.atom value) (hom.maps_tuples tuple present)
  exact (hom.tupleHolds_mapped_iff ground tuple world compatible).mp mappedHolds

end SemanticHom

/-- A semantic isomorphism is a denotation-preserving bijection of typed atoms
    with tuple-preserving maps in both directions. Tuple and atom list order is
    deliberately irrelevant. -/
public structure SemanticIso {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (left : SemanticInstance.{u, v, w, x} context signature Carrier)
    (right : SemanticInstance.{u, v, w, y} context signature Carrier) where
  forward : SemanticHom left right
  backward : SemanticHom right left
  left_inverse : ∀ {type} (value : left.Atom type),
    ({ type := type, value } : TypedAtom left.Atom) ∈ left.atoms →
      backward.atom (forward.atom value) = value
  right_inverse : ∀ {type} (value : right.Atom type),
    ({ type := type, value } : TypedAtom right.Atom) ∈ right.atoms →
      forward.atom (backward.atom value) = value

namespace SemanticIso

/-- Every semantic instance is isomorphic to itself. -/
public def refl {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (data : SemanticInstance.{u, v, w, x} context signature Carrier) :
    SemanticIso data data where
  forward := SemanticHom.refl data
  backward := SemanticHom.refl data
  left_inverse := by simp [SemanticHom.refl]
  right_inverse := by simp [SemanticHom.refl]

/-- Reverse a semantic isomorphism. -/
public def symm {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {left : SemanticInstance.{u, v, w, x} context signature Carrier}
    {right : SemanticInstance.{u, v, w, y} context signature Carrier}
    (iso : SemanticIso left right) : SemanticIso right left where
  forward := iso.backward
  backward := iso.forward
  left_inverse := iso.right_inverse
  right_inverse := iso.left_inverse

/-- Compose semantic isomorphisms. -/
public def trans {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {first : SemanticInstance.{u, v, w, x} context signature Carrier}
    {second : SemanticInstance.{u, v, w, y} context signature Carrier}
    {third : SemanticInstance.{u, v, w, z} context signature Carrier}
    (left : SemanticIso first second) (right : SemanticIso second third) :
    SemanticIso first third where
  forward := right.forward.comp left.forward
  backward := left.backward.comp right.backward
  left_inverse := by
    intro type value present
    simp only [SemanticHom.comp]
    rw [right.left_inverse (left.forward.atom value)
      (left.forward.maps_atoms value present), left.left_inverse value present]
  right_inverse := by
    intro type value present
    simp only [SemanticHom.comp]
    rw [left.right_inverse (right.backward.atom value)
      (right.backward.maps_atoms value present), right.right_inverse value present]

/-- Isomorphic semantic instances have exactly the same completion property. -/
public theorem completes_iff {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {left : SemanticInstance.{u, v, w, x} context signature Carrier}
    {right : SemanticInstance.{u, v, w, y} context signature Carrier}
    (iso : SemanticIso left right) (ground : World → GroundInstance signature Carrier) :
    Completes context left ground ↔ Completes context right ground := by
  constructor
  · exact iso.backward.completes_source ground
  · exact iso.forward.completes_source ground

end SemanticIso

/-- Structural agreement between two relational descriptions means semantic
    isomorphism, rather than equality of fresh IDs or serialization order. -/
public abbrev StructurallyAgrees {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (left : SemanticInstance.{u, v, w, x} context signature Carrier)
    (right : SemanticInstance.{u, v, w, y} context signature Carrier) : Prop :=
  Nonempty (SemanticIso left right)

/-- Two independently produced instances agree when each is isomorphic to
    the same reference structure. This algebraic helper does not prove that
    either producer realizes the reference; a producer-specific theorem must
    establish those facts. -/
public theorem structurallyAgrees_of_common_reference {World : Type u}
    {SemanticType : Type v} {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {left : SemanticInstance.{u, v, w, x} context signature Carrier}
    {right : SemanticInstance.{u, v, w, y} context signature Carrier}
    {reference : SemanticInstance.{u, v, w, z} context signature Carrier}
    (leftReference : SemanticIso left reference)
    (rightReference : SemanticIso right reference) :
    StructurallyAgrees left right :=
  ⟨leftReference.trans rightReference.symm⟩

/-- Structural agreement implies that computation- and proof-derived
    instances make the same positive semantic claims. -/
public theorem structuralAgreement_completes_iff {World : Type u}
    {SemanticType : Type v} {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {left : SemanticInstance.{u, v, w, x} context signature Carrier}
    {right : SemanticInstance.{u, v, w, y} context signature Carrier}
    (agreement : StructurallyAgrees left right)
    (ground : World → GroundInstance signature Carrier) :
    Completes context left ground ↔ Completes context right ground := by
  obtain ⟨iso⟩ := agreement
  exact iso.completes_iff ground

end SpytialLean.Metatheory

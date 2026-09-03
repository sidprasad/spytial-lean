module

public import SpytialLeanMetatheory.LeanExprMeaning
public import SpytialLeanMetatheory.ComputedRelationalization
public import SpytialLeanMetatheory.SemanticIsomorphism
public meta import SpytialLean.InContext

public section

/-!
# Agreement between inspection and relationalization

An equality retained by IYKYK lets inspection use a value that computation
alone cannot obtain from the selected term. The existing structural walker
then reports a finite, positive part of the ordinary relationalization of
that value. This file proves that the reported part embeds in ordinary
relationalization, and that full field coverage upgrades the embedding to an
isomorphism.
-/

namespace SpytialLean.Metatheory

open Lean

universe u v w x y

/-- A change of atom representation. The two runs may use different generated
    identifiers, while the represented typed values remain in bijection. -/
public structure AtomRenaming {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (whole : SemanticInstance.{u, v, w, x} context signature Carrier) where
  Atom : SemanticType → Type y
  encode : ∀ {type}, whole.Atom type → Atom type
  decode : ∀ {type}, Atom type → whole.Atom type
  decode_encode : ∀ {type} (value : whole.Atom type), decode (encode value) = value

namespace AtomRenaming

/-- Reusing the same atom representation is a valid renaming. -/
public def refl {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (whole : SemanticInstance.{u, v, w, x} context signature Carrier) :
    AtomRenaming.{u, v, w, x, x} whole where
  Atom := whole.Atom
  encode := fun value => value
  decode := fun value => value
  decode_encode := by simp

end AtomRenaming

/-- A structurally closed selection from an ordinary relational instance.
    Keeping a tuple requires keeping every atom used by that tuple. -/
public structure StructuralSelection {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (whole : SemanticInstance.{u, v, w, x} context signature Carrier) where
  keepAtom : TypedAtom whole.Atom → Bool
  keepTuple : RelationalTuple signature whole.Atom → Bool
  keepsTupleAtoms : ∀ tuple, tuple ∈ whole.tuples → keepTuple tuple = true →
    ∀ atom, atom ∈ tuple.atoms → keepAtom atom = true

namespace StructuralSelection

/-- The semantic root structure reported by a selection, with the atom names
    chosen by the inspection run. -/
public abbrev rootStruct {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {whole : SemanticInstance.{u, v, w, x} context signature Carrier}
    (selection : StructuralSelection whole)
    (names : AtomRenaming.{u, v, w, x, y} whole) :
    SemanticInstance.{u, v, w, y} context signature Carrier where
  Atom := names.Atom
  denote := fun atom world compatible => whole.denote (names.decode atom) world compatible
  atoms := (whole.atoms.filter selection.keepAtom).map (TypedAtom.map names.encode)
  tuples := (whole.tuples.filter selection.keepTuple).map
    (RelationalTuple.map names.encode)
  tuplesUseKnownAtoms := by
    intro tuple present atom used
    obtain ⟨sourceTuple, sourcePresent, rfl⟩ := List.mem_map.mp present
    rw [RelationalTuple.atoms_map] at used
    obtain ⟨sourceAtom, sourceAtomUsed, rfl⟩ := List.mem_map.mp used
    obtain ⟨tuplePresent, kept⟩ := List.mem_filter.mp sourcePresent
    apply List.mem_map.mpr
    refine ⟨sourceAtom, List.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact whole.tuplesUseKnownAtoms sourceTuple tuplePresent sourceAtom sourceAtomUsed
    · exact selection.keepsTupleAtoms sourceTuple tuplePresent kept sourceAtom sourceAtomUsed

/-- Every partial root inspection embeds in ordinary relationalization. This
    is derived from filtering; tuple inclusion is not a theorem premise. -/
public def inclusion {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {whole : SemanticInstance.{u, v, w, x} context signature Carrier}
    (selection : StructuralSelection whole)
    (names : AtomRenaming.{u, v, w, x, y} whole) :
    SemanticHom (selection.rootStruct names) whole where
  atom := names.decode
  preserves_denotation := by simp [rootStruct]
  maps_atoms := by
    intro type value present
    obtain ⟨source, sourcePresent, equal⟩ := List.mem_map.mp present
    cases equal
    rcases source with ⟨sourceType, sourceValue⟩
    rw [names.decode_encode]
    exact (List.mem_filter.mp sourcePresent).1
  maps_tuples := by
    intro tuple present
    obtain ⟨source, sourcePresent, rfl⟩ := List.mem_map.mp present
    rw [RelationalTuple.map_leftInverse names.encode names.decode
      names.decode_encode]
    exact (List.mem_filter.mp sourcePresent).1

/-- Stopping early preserves soundness because the renamed root slice maps
    back into the sound ordinary relationalization. -/
public theorem rootStruct_sound {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {whole : SemanticInstance.{u, v, w, x} context signature Carrier}
    (selection : StructuralSelection whole)
    (names : AtomRenaming.{u, v, w, x, y} whole)
    (ground : World → GroundInstance signature Carrier)
    (wholeSound : Completes context whole ground) :
    Completes context (selection.rootStruct names) ground :=
  (selection.inclusion names).completes_source ground wholeSound

/-- Field coverage means that the root walk retained every atom and tuple
    produced by ordinary relationalization. -/
public abbrev Covers {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {whole : SemanticInstance.{u, v, w, x} context signature Carrier}
    (selection : StructuralSelection whole) : Prop :=
  (∀ atom, atom ∈ whole.atoms → selection.keepAtom atom = true) ∧
    (∀ tuple, tuple ∈ whole.tuples → selection.keepTuple tuple = true)

/-- Full field coverage makes root inspection isomorphic to ordinary
    relationalization. -/
public def isoOfCoverage {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {whole : SemanticInstance.{u, v, w, x} context signature Carrier}
    (selection : StructuralSelection whole)
    (names : AtomRenaming.{u, v, w, x, y} whole)
    (coverage : selection.Covers) :
    SemanticIso (selection.rootStruct names) whole where
  forward := selection.inclusion names
  backward := {
    atom := names.encode
    preserves_denotation := by
      intro type value world compatible
      change whole.denote (names.decode (names.encode value)) world compatible =
        whole.denote value world compatible
      rw [names.decode_encode]
    maps_atoms := by
      intro type value present
      apply List.mem_map.mpr
      exact ⟨{ type, value },
        List.mem_filter.mpr ⟨present, coverage.1 { type, value } present⟩, rfl⟩
    maps_tuples := by
      intro tuple present
      apply List.mem_map.mpr
      exact ⟨tuple, List.mem_filter.mpr ⟨present, coverage.2 tuple present⟩, rfl⟩ }
  left_inverse := by
    intro type value present
    obtain ⟨source, _, equal⟩ := List.mem_map.mp present
    cases equal
    rcases source with ⟨sourceType, sourceValue⟩
    change names.encode (names.decode (names.encode sourceValue)) = names.encode sourceValue
    rw [names.decode_encode]
  right_inverse := by
    intro type value _
    exact names.decode_encode value

/-- The unbounded, successful selection used for an already computed value. -/
public def all {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (whole : SemanticInstance.{u, v, w, x} context signature Carrier) :
    StructuralSelection whole where
  keepAtom := fun _ => true
  keepTuple := fun _ => true
  keepsTupleAtoms := by simp

public theorem all_covers {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (whole : SemanticInstance.{u, v, w, x} context signature Carrier) :
    (all whole).Covers := by
  constructor <;> simp [all]

end StructuralSelection

/-- An equality refinement selected from an actual `Afaik` result. The fact
    is retained proof-backed knowledge about the selected root, in either
    equation orientation accepted by the production refinement finder. -/
public structure ProductionRefinement {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning.{u, v} World context) (knowledge : Iykyk.Afaik) where
  fact : Iykyk.KnownFact
  fact_mem : fact ∈ knowledge.facts
  type : Expr
  value : Expr
  root_checked : meaning.hasType knowledge.root type
  value_checked : meaning.hasType value type
  shape : fact.proposition.eq? = some (type, knowledge.root, value) ∨
    fact.proposition.eq? = some (type, value, knowledge.root)
  proof_checked : meaning.proofChecks fact.proposition fact.proof

namespace ProductionRefinement

@[expose] public def rootTerm {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (refinement : ProductionRefinement meaning knowledge) :
    LeanExprMeaning.CheckedTerm meaning where
  expression := knowledge.root
  type := refinement.type
  checked := refinement.root_checked

@[expose] public def valueTerm {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (refinement : ProductionRefinement meaning knowledge) :
    LeanExprMeaning.CheckedTerm meaning where
  expression := refinement.value
  type := refinement.type
  checked := refinement.value_checked

/-- Kernel proof soundness and the semantics of Lean's actual `Eq` expression
    establish that the selected root denotes the refined value. -/
public theorem root_denote_eq {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (refinement : ProductionRefinement meaning knowledge) (world : World)
    (compatible : context world) :
    refinement.rootTerm.denote world compatible =
      refinement.valueTerm.denote world compatible := by
  have propositionHolds := meaning.proofChecks_sound refinement.proof_checked
    world compatible
  rcases refinement.shape with forward | backward
  · exact meaning.equality_sound forward refinement.root_checked
      refinement.value_checked world compatible propositionHolds
  · exact (meaning.equality_sound backward refinement.value_checked
      refinement.root_checked world compatible propositionHolds).symm

/-- The partial computation/proof bridge. A value obtained from a retained
    equality has the same denotation as the selected root, and every reported
    root tuple embeds in ordinary relationalization of that value. -/
public theorem partial_bridge {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {meaning : LeanExprMeaning.{u, x} World context} {knowledge : Iykyk.Afaik}
    (refinement : ProductionRefinement meaning knowledge)
    (relationalize : LeanExprMeaning.CheckedTerm meaning →
      SemanticInstance.{u, v, w, x} context signature Carrier)
    (selection : StructuralSelection (relationalize refinement.valueTerm))
    (names : AtomRenaming.{u, v, w, x, y}
      (relationalize refinement.valueTerm)) :
    (∀ world (compatible : context world),
      refinement.rootTerm.denote world compatible =
        refinement.valueTerm.denote world compatible) ∧
      Nonempty (SemanticHom (selection.rootStruct names)
        (relationalize refinement.valueTerm)) :=
  ⟨refinement.root_denote_eq, ⟨selection.inclusion names⟩⟩

/-- The complete computation/proof bridge. If the root walk covers every
    ordinary atom and structural tuple, proof-aware inspection and computation
    expose isomorphic relational instances. -/
public theorem full_bridge {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    {meaning : LeanExprMeaning.{u, x} World context} {knowledge : Iykyk.Afaik}
    (refinement : ProductionRefinement meaning knowledge)
    (relationalize : LeanExprMeaning.CheckedTerm meaning →
      SemanticInstance.{u, v, w, x} context signature Carrier)
    (selection : StructuralSelection (relationalize refinement.valueTerm))
    (names : AtomRenaming.{u, v, w, x, y}
      (relationalize refinement.valueTerm))
    (coverage : selection.Covers) :
    (∀ world (compatible : context world),
      refinement.rootTerm.denote world compatible =
        refinement.valueTerm.denote world compatible) ∧
      StructurallyAgrees (selection.rootStruct names)
        (relationalize refinement.valueTerm) :=
  ⟨refinement.root_denote_eq, ⟨selection.isoOfCoverage names coverage⟩⟩

/-- The packaged headline result. A checked structural trace proves ordinary
    relationalization sound in the generated production ground. If the
    proof-guided root walk has full coverage, the selected term denotes the
    computed value, its inspected root tuples are sound in that same model,
    and the relational structures are isomorphic up to atom names. -/
public theorem full_inspect_bridge {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (refinement : ProductionRefinement meaning knowledge)
    (relationalize : LeanExprMeaning.CheckedTerm meaning →
      List (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)))
    (selection : StructuralSelection
      (meaning.instanceOfTuples (relationalize refinement.valueTerm)))
    (names : AtomRenaming
      (meaning.instanceOfTuples (relationalize refinement.valueTerm)))
    (coverage : selection.Covers)
    {trace : SpytialLean.TracedDataInstance}
    {checked : SpytialLean.CheckedStructuralTrace trace}
    (required : StructuralRequirement
      (signature := meaning.signature)
      (Entry := (meaning.instanceOfTuples
        (relationalize refinement.valueTerm)).Atom))
    (computed : ComputedStructuralCertificate meaning trace
      (relationalize refinement.valueTerm) required checked) :
    (∀ world (compatible : context world),
      refinement.rootTerm.denote world compatible =
        refinement.valueTerm.denote world compatible) ∧
      Completes context (selection.rootStruct names)
        (ProductionTupleHolds.ground meaning) ∧
      StructurallyAgrees (selection.rootStruct names)
        (meaning.instanceOfTuples (relationalize refinement.valueTerm)) :=
  ⟨refinement.root_denote_eq,
    selection.rootStruct_sound names (ProductionTupleHolds.ground meaning)
      computed.adequate,
    ⟨selection.isoOfCoverage names coverage⟩⟩

end ProductionRefinement

/-- Conservativity for computed values. A complete structural inspection of
    a value agrees with its ordinary relationalization. -/
public theorem computed_value_agreement {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (data : SemanticInstance.{u, v, w, x} context signature Carrier)
    (names : AtomRenaming.{u, v, w, x, y} data) :
    StructurallyAgrees ((StructuralSelection.all data).rootStruct names) data :=
  ⟨(StructuralSelection.all data).isoOfCoverage names
    (StructuralSelection.all_covers data)⟩

end SpytialLean.Metatheory

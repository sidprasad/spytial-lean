module

public import SpytialLeanMetatheory.LeanExprMeaning
public import SpytialLeanMetatheory.RootedTrace
public import SpytialLeanMetatheory.SemanticIsomorphism
public meta import SpytialLean.InContext

public section

/-!
# Agreement between inspection and relationalization

An equality retained by IYKYK lets inspection use a value that computation
alone cannot obtain from the selected term. The existing structural walker
then reports a finite, positive part of the ordinary relationalization of
that value. This file proves that the reported part agrees with computation on
everything it reports, and that full field coverage gives the same relational
structure. The public results are named for those semantic claims; trace and
representation machinery remains supporting code.
-/

namespace SpytialLean.Metatheory

open Lean

universe u v w x y

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

end ProductionRefinement

/-- Two relational descriptions have the same typed structure when they are
    isomorphic after generated atom names and tuple order are ignored. -/
public abbrev SameRelationalStructure {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (left : SemanticInstance.{u, v, w, x} context signature Carrier)
    (right : SemanticInstance.{u, v, w, y} context signature Carrier) : Prop :=
  StructurallyAgrees left right

namespace RelationalInspection

/-- Change only the generated identifier of an expression-backed atom. Its
    Lean term, type, and denotation are unchanged. -/
@[expose] public def renameAtom {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {type : meaning.TypeCode}
    (rename : String → String) (atom : LeanExprMeaning.ExprAtom meaning type) :
    LeanExprMeaning.ExprAtom meaning type :=
  { atom with id := rename atom.id }

/-- Concrete, checkable evidence that every tuple in one production result
    occurs in another after generated atom identifiers are renamed. -/
public structure ReportedStructure {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning.{u, v} World context)
    (source target : List
      (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning))) where
  rename : String → String
  maps_tuples : ∀ tuple, tuple ∈ source →
    tuple.map (renameAtom rename) ∈ target

namespace ReportedStructure

/-- Tuple correspondence induces a denotation-preserving map of the semantic
    instances. Atom preservation follows because each instance contains
    exactly the atoms used by its tuples. -/
public def semanticMap {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context}
    {source target : List
      (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning))}
    (reported : ReportedStructure meaning source target) :
    SemanticHom (meaning.instanceOfTuples source) (meaning.instanceOfTuples target) where
  atom := renameAtom reported.rename
  preserves_denotation := by
    intro type value world compatible
    simp [LeanExprMeaning.instanceOfTuples, SemanticInstance.ofTuples,
      renameAtom, LeanExprMeaning.ExprAtom.denote]
  maps_atoms := by
    intro type value present
    change ({ type, value } : TypedAtom (LeanExprMeaning.ExprAtom meaning)) ∈
      source.flatMap RelationalTuple.atoms at present
    change ({ type, value := renameAtom reported.rename value } :
      TypedAtom (LeanExprMeaning.ExprAtom meaning)) ∈
        target.flatMap RelationalTuple.atoms
    simp only [List.mem_flatMap] at present ⊢
    obtain ⟨tuple, tuplePresent, atomPresent⟩ := present
    refine ⟨tuple.map (renameAtom reported.rename),
      reported.maps_tuples tuple tuplePresent, ?_⟩
    rw [RelationalTuple.atoms_map]
    exact List.mem_map.mpr ⟨{ type, value }, atomPresent, rfl⟩
  maps_tuples := reported.maps_tuples

end ReportedStructure

/-- Completion evidence for a reported structure. It says that computation
    contains no additional tuple and supplies the inverse identifier renaming
    on active atoms. Unlike `SemanticIso`, these fields contain no denotational
    or semantic truth assumptions. -/
public structure CompleteCoverage {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning.{u, v} World context)
    (left right : List
      (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)))
    (reported : ReportedStructure meaning left right) where
  renameBack : String → String
  covers_computation : ∀ tuple, tuple ∈ right →
    tuple.map (renameAtom renameBack) ∈ left
  left_inverse : ∀ {type} (atom : LeanExprMeaning.ExprAtom meaning type),
    ({ type, value := atom } : TypedAtom (LeanExprMeaning.ExprAtom meaning)) ∈
        (meaning.instanceOfTuples left).atoms →
      renameAtom renameBack (renameAtom reported.rename atom) = atom
  right_inverse : ∀ {type} (atom : LeanExprMeaning.ExprAtom meaning type),
    ({ type, value := atom } : TypedAtom (LeanExprMeaning.ExprAtom meaning)) ∈
        (meaning.instanceOfTuples right).atoms →
      renameAtom reported.rename (renameAtom renameBack atom) = atom

namespace CompleteCoverage

/-- Syntactic tuple and identifier correspondence implies semantic
    isomorphism. Denotation preservation is derived because renaming changes
    no Lean term. -/
public def semanticIso {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context}
    {left right : List
      (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning))}
    {reported : ReportedStructure meaning left right}
    (complete : CompleteCoverage meaning left right reported) :
    SemanticIso (meaning.instanceOfTuples left) (meaning.instanceOfTuples right) where
  forward := reported.semanticMap
  backward := ({
    rename := complete.renameBack
    maps_tuples := complete.covers_computation
  } : ReportedStructure meaning right left).semanticMap
  left_inverse := complete.left_inverse
  right_inverse := complete.right_inverse

end CompleteCoverage

/-- One proof-guided inspection together with ordinary computation of the
    value established by its retained equality. Its correspondence contains
    only tuple membership and generated-name replacement for the two actual
    checked traces. -/
public structure KnownValue {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning.{u, v} World context) (knowledge : Iykyk.Afaik) where
  contextualTrace : SpytialLean.TracedDataInstance
  contextualChecked : CheckedCoreTrace contextualTrace
  contextualEvidence : ProductionEvidenceMeaning meaning
  contextualSelectorEvidence : SpytialLean.SelectorEvidence
  root : String
  computedTrace : SpytialLean.TracedDataInstance
  computedChecked : SpytialLean.CheckedStructuralTrace computedTrace
  computedEvidence : ProductionEvidenceMeaning meaning
  computedSelectorEvidence : SpytialLean.SelectorEvidence
  computedRoot : String
  equality : ProductionRefinement meaning knowledge
  contextual_root_names_term :
    (equality.rootTerm.expression, root) ∈ contextualSelectorEvidence.terms
  computed_root_names_value :
    (equality.valueTerm.expression, computedRoot) ∈ computedSelectorEvidence.terms
  reported : ReportedStructure meaning
    (rootedStructuralTuples contextualChecked.structural contextualEvidence root)
    (rootedStructuralTuples computedChecked computedEvidence computedRoot)
  reported_root : reported.rename root = computedRoot

namespace KnownValue

/-- The proof-aware semantic inspection reconstructed from the actual rooted
    production trace. -/
@[expose] public noncomputable def inspection {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) : Inspection meaning :=
  known.contextualChecked.rootedInspection known.contextualEvidence known.root

/-- Ordinary semantic relationalization reconstructed from the actual checked
    computed-value trace. -/
@[expose] public noncomputable def computation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :
    SemanticInstance context meaning.signature meaning.Carrier :=
  meaning.instanceOfTuples
    (rootedStructuralTuples known.computedChecked known.computedEvidence known.computedRoot)

/-- The retained equality really identifies the inspected root with the value
    used by ordinary computation. -/
public theorem denotes_same_value {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) (world : World)
    (compatible : context world) :
    known.equality.rootTerm.denote world compatible =
      known.equality.valueTerm.denote world compatible :=
  known.equality.root_denote_eq world compatible

/-- Every tuple reported by this actual rooted inspection is justified by its
    checked structural or proof origin. -/
public theorem sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :
    Completes context known.inspection.data (ProductionTupleHolds.ground meaning) :=
  known.contextualChecked.rootedInspection_sound known.contextualEvidence known.root

end KnownValue

/-- A complete proof-guided inspection reports every atom and tuple exposed by
    ordinary structural relationalization of its known value. -/
public structure CompleteKnownValue {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning.{u, v} World context) (knowledge : Iykyk.Afaik) where
  toKnownValue : KnownValue meaning knowledge
  coverage : CompleteCoverage meaning
    (rootedStructuralTuples toKnownValue.contextualChecked.structural
      toKnownValue.contextualEvidence toKnownValue.root)
    (rootedStructuralTuples toKnownValue.computedChecked
      toKnownValue.computedEvidence toKnownValue.computedRoot)
    toKnownValue.reported

/-- The semantic content of knowledge-source independence. The checked
    equality identifies the two roots as values, while the relational
    isomorphism identifies everything the supported walks report about them. -/
public structure KnowledgeSourceIndependent {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) : Prop where
  same_value : ∀ world (compatible : context world),
    known.equality.rootTerm.denote world compatible =
      known.equality.valueTerm.denote world compatible
  same_structure : SameRelationalStructure known.inspection.rootStruct known.computation

/-- Partial inspections agree with computation on everything that they
    report. This one-way result does not require an inverse atom renaming. -/
public theorem agrees_with_computation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :
    Nonempty (SemanticHom known.inspection.rootStruct known.computation) := by
  exact ⟨known.reported.semanticMap⟩

/-- **Knowledge-source independence.** If the context establishes a value and
    proof-guided inspection completely exposes its supported root structure,
    the result has the same typed relational structure as ordinary computation
    of that value. Thus the relational interface does not depend on whether
    Lean obtained the value by computation or by proof. -/
public theorem knowledge_source_independence {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : CompleteKnownValue meaning knowledge) :
    KnowledgeSourceIndependent known.toKnownValue where
  same_value := known.toKnownValue.denotes_same_value
  same_structure := ⟨known.coverage.semanticIso⟩

end RelationalInspection

end SpytialLean.Metatheory

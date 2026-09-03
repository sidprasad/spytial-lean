module

public import SpytialLeanMetatheory.LeanExprMeaning
public import SpytialLeanMetatheory.ProofDecoder
public meta import SpytialLean.InContext

public section

/-!
# Connecting production proof traces to semantics

`SpytialLean.checkedProvedOrigins` runs on the trace and selector evidence
returned by the real proof-context relationalizer. It rechecks the proof,
reruns the proposition decoder, retains the actual relation head and Lean
column types, and checks that every decoded term names the recorded atom.

The remaining semantic obligation is direct: in an interpretation satisfying
the Lean context, truth of the decoded proposition must imply truth of the
emitted tuple. Together with a typed interpretation of the trace, this
obligation connects the checked origins to the existing `ProofDecoding`
result.
-/

namespace SpytialLean.Metatheory

open Lean SpytialLean

universe u v

namespace LeanExprMeaning

/-- A semantic instance made from expression-backed tuples. -/
@[expose] public def instanceOfTuples {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context)
    (tuples : List (RelationalTuple meaning.signature (ExprAtom meaning))) :
    SemanticInstance context meaning.signature meaning.Carrier :=
  SemanticInstance.ofTuples context meaning.signature meaning.Carrier
    (ExprAtom meaning) ExprAtom.denote tuples

end LeanExprMeaning

/-- Unfold the expression-backed signature at a relation symbol. -/
@[expose] public def exprRelation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (relation : meaning.signature.Relation) : LeanExprMeaning.ExprRelation meaning :=
  relation

/-- The production atom identifiers used by one expression-backed tuple. -/
@[expose] public def exprTupleAtomIds {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) :
    List String :=
  tuple.atoms.map fun atom => atom.value.id

/-- Reusing a production atom identifier means reusing one typed semantic
    atom, including across different tuples. -/
public def ExprAtomIdsAreShared {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context)
    (tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))) : Prop :=
  ∀ {leftType rightType : meaning.TypeCode}
    (left : LeanExprMeaning.ExprAtom meaning leftType)
    (right : LeanExprMeaning.ExprAtom meaning rightType),
    ({ type := leftType, value := left } :
      TypedAtom (LeanExprMeaning.ExprAtom meaning)) ∈
        (meaning.instanceOfTuples tuples).atoms →
    ({ type := rightType, value := right } :
      TypedAtom (LeanExprMeaning.ExprAtom meaning)) ∈
        (meaning.instanceOfTuples tuples).atoms →
    left.id = right.id → HEq left right

/-- The local semantic facts for one checked production origin and one typed
    tuple. They state exactly what the runtime checks established and the one
    semantic fact the expression interpreter must establish. -/
public structure ProvedTupleRealization {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context)
    (ground : World → GroundInstance meaning.signature meaning.Carrier)
    (tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning)))
    (source : Iykyk.Metatheory.Fact World) (origin : CheckedProvedOrigin)
    (tuple : RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) where
  relation_name : (exprRelation tuple.relation).name = origin.relation
  relation_head : (exprRelation tuple.relation).head =
    Quotient.mk meaning.defEq origin.head
  relation_parameters : (exprRelation tuple.relation).parameters =
    origin.parameters.toList.map fun parameter => Quotient.mk meaning.defEq parameter
  column_types : (exprRelation tuple.relation).columns =
    origin.types.toList.map fun type => Quotient.mk meaning.defEq type
  atom_ids : exprTupleAtomIds tuple = origin.atoms.toList
  proof_checked : meaning.proofChecks origin.proposition origin.proof
  source_is_proposition : source = meaning.proposition origin.proposition
  proposition_implies_tuple : ∀ world (compatible : context world),
    meaning.proposition origin.proposition world →
      (meaning.instanceOfTuples tuples).TupleHolds ground tuple world compatible

/-- The checked runtime facts required to interpret all proof-derived tuples.
    Each tuple has one emitted checked origin and one local realization above;
    shared atom IDs and IYKYK membership are global properties. -/
public structure ProductionProofRealization {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context)
    (knowledge : Iykyk.Metatheory.Knowledge World Root)
    (ground : World → GroundInstance meaning.signature meaning.Carrier)
    (tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning)))
    (trace : TracedDataInstance)
    (checked : CheckedProofTrace trace) where
  atom_ids_are_shared : ExprAtomIdsAreShared meaning tuples
  source : RelationalTuple meaning.signature
    (LeanExprMeaning.ExprAtom meaning) → Iykyk.Metatheory.Fact World
  origin : ∀ tuple, tuple ∈ tuples → CheckedProvedOrigin
  origin_was_checked : ∀ tuple (present : tuple ∈ tuples),
    origin tuple present ∈ checked.origins.toList
  origin_was_emitted : ∀ tuple (present : tuple ∈ tuples),
    (origin tuple present).emission ∈ trace.emissions
  tuple_realization : ∀ tuple (present : tuple ∈ tuples),
    ProvedTupleRealization meaning ground tuples (source tuple)
      (origin tuple present) tuple
  source_is_known : ∀ tuple ∈ tuples, source tuple ∈ knowledge.facts

namespace ProductionProofRealization

/-- The checked Lean proof entails the semantic source fact. This is the
    explicit point where the model relies on Lean's proof checker. -/
public theorem source_sound {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {ground : World → GroundInstance meaning.signature meaning.Carrier}
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {trace : TracedDataInstance}
    {checked : CheckedProofTrace trace}
    (realization : ProductionProofRealization meaning knowledge ground tuples trace checked)
    {tuple} (present : tuple ∈ tuples) :
    Iykyk.Metatheory.Entails context (realization.source tuple) := by
  let tupleRealization := realization.tuple_realization tuple present
  rw [tupleRealization.source_is_proposition]
  exact meaning.proofChecks_sound tupleRealization.proof_checked

/-- Checked `proved` origins from the production proposition decoder
    instantiate the abstract `ProofDecoding` interface. -/
public def toProofDecoding {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {ground : World → GroundInstance meaning.signature meaning.Carrier}
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {trace : TracedDataInstance}
    {checked : CheckedProofTrace trace}
    (realization : ProductionProofRealization meaning knowledge ground tuples trace checked) :
    ProofDecoding knowledge (meaning.instanceOfTuples tuples) ground where
  source := realization.source
  source_mem := realization.source_is_known
  reflects := by
    intro tuple present world compatible sourceHolds
    let tupleRealization := realization.tuple_realization tuple present
    have propositionHolds : meaning.proposition
        (realization.origin tuple present).proposition world := by
      rw [← tupleRealization.source_is_proposition]
      exact sourceHolds
    exact tupleRealization.proposition_implies_tuple world compatible propositionHolds

/-- Therefore every proof-derived production tuple is true in every world
    compatible with sound IYKYK knowledge. -/
public theorem sound {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {ground : World → GroundInstance meaning.signature meaning.Carrier}
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {trace : TracedDataInstance}
    {checked : CheckedProofTrace trace}
    (realization : ProductionProofRealization meaning knowledge ground tuples trace checked)
    (knowledgeSound : knowledge.Sound context) :
    Completes context (meaning.instanceOfTuples tuples) ground :=
  realization.toProofDecoding.sound knowledgeSound

end ProductionProofRealization

end SpytialLean.Metatheory

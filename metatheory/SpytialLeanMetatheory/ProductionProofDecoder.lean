module

public import SpytialLeanMetatheory.ProofDecoder
public import SpytialLeanMetatheory.ProductionRelationSemantics

public section

/-!
# Connecting production proof traces to semantics

`SpytialLean.checkedProvedOrigins` runs on the trace and selector evidence
returned by the real proof-context relationalizer. It rechecks the proof,
reruns the proposition decoder, retains the actual relation head and Lean
column types, and checks that every decoded term names the recorded atom.

The executable checks do not by themselves interpret Lean expressions. A
semantic realization must still build typed tuples and preserve shared atom
identifiers. The production relation judgment gives structural and proved
tuples one shared meaning; individual tuple realizations contain no soundness
premise.
-/

namespace SpytialLean.Metatheory

open Lean SpytialLean

universe u v

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

/-- The interpretation of all proof-derived tuples from one checked trace.
    Each tuple has one emitted checked origin and one local realization above;
    shared atom IDs and IYKYK membership are global properties. -/
public structure ProductionProofRealization {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context)
    (knowledge : Iykyk.Metatheory.Knowledge World Root)
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
    ProvedTupleRealization meaning (origin tuple present) tuple
  source_is_proposition : ∀ tuple (present : tuple ∈ tuples),
    source tuple = meaning.proposition (origin tuple present).proposition
  source_is_known : ∀ tuple ∈ tuples, source tuple ∈ knowledge.facts

namespace ProductionProofRealization

/-- The checked Lean proof entails the semantic source fact. This is the
    explicit point where the model relies on Lean's proof checker. -/
public theorem source_sound {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {trace : TracedDataInstance}
    {checked : CheckedProofTrace trace}
    (realization : ProductionProofRealization meaning knowledge tuples trace checked)
    {tuple} (present : tuple ∈ tuples) :
    Iykyk.Metatheory.Entails context (realization.source tuple) := by
  let tupleRealization := realization.tuple_realization tuple present
  rw [realization.source_is_proposition tuple present]
  exact meaning.proofChecks_sound tupleRealization.proof_checked

/-- A completed realization of checked `proved` origins instantiates the
    abstract `ProofDecoding` interface. -/
public def toProofDecoding {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {trace : TracedDataInstance}
    {checked : CheckedProofTrace trace}
    (realization : ProductionProofRealization meaning knowledge tuples trace checked) :
    ProofDecoding knowledge (meaning.instanceOfTuples tuples)
      (ProductionTupleHolds.ground meaning) where
  source := realization.source
  source_mem := realization.source_is_known
  reflects := by
    intro tuple present world compatible sourceHolds
    let tupleRealization := realization.tuple_realization tuple present
    have propositionHolds : meaning.proposition
        (realization.origin tuple present).proposition world := by
      rw [← realization.source_is_proposition tuple present]
      exact sourceHolds
    exact ProductionTupleHolds.provedTupleHolds tupleRealization world compatible
      propositionHolds

/-- Therefore every proof-derived production tuple is true in every compatible
    world. This uses the rechecked proof stored in each production origin. -/
public theorem sound {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {tuples : List (RelationalTuple meaning.signature
      (LeanExprMeaning.ExprAtom meaning))}
    {trace : TracedDataInstance}
    {checked : CheckedProofTrace trace}
    (realization : ProductionProofRealization meaning knowledge tuples trace checked) :
    Completes context (meaning.instanceOfTuples tuples)
      (ProductionTupleHolds.ground meaning) := by
  intro world compatible tuple present
  exact ProductionTupleHolds.checkedProvedTupleHolds
    (realization.tuple_realization tuple present) world compatible

end ProductionProofRealization

end SpytialLean.Metatheory

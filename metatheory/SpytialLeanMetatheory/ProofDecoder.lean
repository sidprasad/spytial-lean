module

public import SpytialLeanMetatheory.SemanticInstance

public section

/-!
# Proof-derived relationalization

IYKYK owns the sound finite knowledge extracted from a proof context. A
Spytial decoder chooses relational facts from that knowledge and turns their
typed terms into shared atoms. The only decoder-specific obligation is
`ProofDecoding.reflects`: the source proposition must imply the emitted tuple.

This isolates the runtime reflection boundary precisely. For an already
semantic atomic relation, `decodeAtomicFacts_sound` discharges reflection by
construction. The remaining implementation theorem is that
`propTupleShape?`, after kernel checking, realizes that atomic decoder.
-/

namespace SpytialLean.Metatheory

universe u v w x

/-- Evidence that a finite semantic instance was decoded from an IYKYK
    knowledge value without strengthening any source fact. -/
public structure ProofDecoding {World : Type u} {Root : Type v}
    {SemanticType : Type w} {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World Root)
    (data : SemanticInstance context signature Carrier)
    (ground : World → GroundInstance signature Carrier) where
  source : RelationalTuple signature data.Atom → Iykyk.Metatheory.Fact World
  source_mem : ∀ tuple, tuple ∈ data.tuples → source tuple ∈ knowledge.facts
  reflects : ∀ tuple, tuple ∈ data.tuples → ∀ world (compatible : context world),
    source tuple world → data.TupleHolds ground tuple world compatible

/-- Possible-world soundness of proof-to-tuple decoding. Every emitted tuple
    is true in every ground structure compatible with the proof context. -/
public theorem ProofDecoding.sound {World : Type u} {Root : Type v}
    {SemanticType : Type w} {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type x}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {data : SemanticInstance context signature Carrier}
    {ground : World → GroundInstance signature Carrier}
    (decoding : ProofDecoding knowledge data ground)
    (knowledgeSound : knowledge.Sound context) : Completes context data ground := by
  intro world compatible tuple present
  exact decoding.reflects tuple present world compatible
    (knowledgeSound (decoding.source_mem tuple present) world compatible)

/-- A proof-derived atom may choose a value separately in every compatible
    possible world. This is the same dependency used by IYKYK's shared
    existential witnesses. -/
public abbrev ContextualAtom {World : Type u} {SemanticType : Type v}
    (context : Iykyk.Metatheory.Context World)
    (Carrier : SemanticType → Type w) (type : SemanticType) :=
  ∀ world, context world → Carrier type

/-- Decode semantic atomic relation facts by reusing their typed terms as
    atoms. The tuple list is finite and remains positive/open-world. -/
@[expose] public def decodeAtomicFacts {World : Type u} {SemanticType : Type v}
    (context : Iykyk.Metatheory.Context World)
    (signature : RelationalSignature SemanticType)
    (Carrier : SemanticType → Type w)
    (facts : List (RelationalTuple signature (ContextualAtom context Carrier))) :
    SemanticInstance context signature Carrier where
  Atom := ContextualAtom context Carrier
  denote := fun atom world compatible => atom world compatible
  atoms := facts.flatMap (·.atoms)
  tuples := facts
  tuplesUseKnownAtoms := by
    intro tuple tupleMem atom atomMem
    induction facts with
    | nil => contradiction
    | cons head tail ih =>
        cases tupleMem with
        | head _ => exact List.mem_append_left _ atomMem
        | tail _ tupleMem =>
            exact List.mem_append_right _ (ih tupleMem)

/-- Atomic decoding has no additional semantic leap: its source fact is
    exactly the proposition denoted by the emitted tuple. -/
public def atomicProofDecoding {World : Type u} {Root : Type v}
    {SemanticType : Type w} {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type x}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {ground : World → GroundInstance signature Carrier}
    (facts : List (RelationalTuple signature (ContextualAtom context Carrier)))
    (known : ∀ tuple ∈ facts,
      (decodeAtomicFacts context signature Carrier facts).tupleFact ground tuple ∈
        knowledge.facts) :
    ProofDecoding knowledge (decodeAtomicFacts context signature Carrier facts) ground where
  source := fun tuple =>
    (decodeAtomicFacts context signature Carrier facts).tupleFact ground tuple
  source_mem := known
  reflects := by
    intro tuple _ world compatible sourceHolds
    exact sourceHolds compatible

/-- The concrete atomic decoder is sound whenever its source facts occur in
    sound IYKYK knowledge. -/
public theorem decodeAtomicFacts_sound {World : Type u} {Root : Type v}
    {SemanticType : Type w} {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type x}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    {ground : World → GroundInstance signature Carrier}
    (facts : List (RelationalTuple signature (ContextualAtom context Carrier)))
    (known : ∀ tuple ∈ facts,
      (decodeAtomicFacts context signature Carrier facts).tupleFact ground tuple ∈
        knowledge.facts)
    (knowledgeSound : knowledge.Sound context) :
    Completes context (decodeAtomicFacts context signature Carrier facts) ground :=
  (atomicProofDecoding facts known).sound knowledgeSound

end SpytialLean.Metatheory

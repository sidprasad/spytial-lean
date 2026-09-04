module

public import SpytialLeanMetatheory.Semantic

public section

/-!
# Proof-derived relational data

IYKYK owns proof extraction and proves that every retained fact follows from
the current context. Spytial Lean decodes the supported relational facts into
typed tuples. This file states the exact seam between those two components:
each decoded tuple points to the corresponding fact already present in IYKYK
knowledge.
-/

namespace SpytialLean.Metatheory

universe u v w x y

/-- The relational subset decoded from one IYKYK knowledge value. The origin
    condition is membership in certified knowledge, not an independent tuple
    truth assumption. -/
public structure DecodedKnowledge {World : Type u} {SemanticType : Type v}
    {Root : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    (interpretation : AtomInterpretation context model Entry)
    (knowledge : Iykyk.Metatheory.Knowledge World Root) where
  tuples : List (RelationalTuple signature Entry)
  from_knowledge : ∀ tuple, tuple ∈ tuples →
    tupleFact interpretation tuple ∈ knowledge.facts

namespace DecodedKnowledge

/-- Forget tuple provenance and obtain ordinary positive relational data. -/
@[expose] public def data {World : Type u} {SemanticType : Type v}
    {Root : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    (decoded : DecodedKnowledge interpretation knowledge) :
    RelationalData signature Entry :=
  RelationalData.ofTuples signature Entry decoded.tuples

/-- IYKYK soundness immediately gives soundness of every decoded tuple. -/
public theorem sound {World : Type u} {SemanticType : Type v}
    {Root : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {knowledge : Iykyk.Metatheory.Knowledge World Root}
    (decoded : DecodedKnowledge interpretation knowledge)
    (knowledgeSound : knowledge.Sound context) :
    Sound context interpretation decoded.data := by
  rw [sound_iff_tuple_facts]
  intro tuple present
  exact knowledgeSound (decoded.from_knowledge tuple present)

/-- A decoder may report no supported relational facts without becoming
    unsound. This is why soundness does not imply extraction completeness. -/
public def empty {World : Type u} {SemanticType : Type v}
    {Root : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    (interpretation : AtomInterpretation context model Entry)
    (knowledge : Iykyk.Metatheory.Knowledge World Root) :
    DecodedKnowledge interpretation knowledge where
  tuples := []
  from_knowledge := by simp

end DecodedKnowledge

end SpytialLean.Metatheory

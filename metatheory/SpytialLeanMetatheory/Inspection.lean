module

public import SpytialLeanMetatheory.ComputedRelationalization
public import SpytialLeanMetatheory.ProductionProofDecoder

public section

/-!
# Relational inspection

An inspection result combines tuples obtained from structural computation
with tuples decoded from checked propositions. Both sources use the same
expression-backed atoms and the same typed relational signature. This file
proves soundness of the combined positive instance and connects that result
to the existing production trace certificates.
-/

namespace SpytialLean.Metatheory

universe u v

/-- The semantic contents of one inspection. The two lists record the source
    of each tuple; `data` below is their ordinary positive union. -/
public structure Inspection {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning World context) where
  structuralTuples : List (RelationalTuple meaning.signature
    (LeanExprMeaning.ExprAtom meaning))
  provedTuples : List (RelationalTuple meaning.signature
    (LeanExprMeaning.ExprAtom meaning))

namespace Inspection

/-- The complete relational interface sent on to Spytial. -/
@[expose] public def data {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (inspection : Inspection meaning) :
    SemanticInstance context meaning.signature meaning.Carrier :=
  meaning.instanceOfTuples (inspection.structuralTuples ++ inspection.provedTuples)

/-- The structural slice rooted at the inspected value. Proof-derived
    predicates remain in `data`, but not in this comparison slice. -/
@[expose] public def rootStruct {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (inspection : Inspection meaning) :
    SemanticInstance context meaning.signature meaning.Carrier :=
  meaning.instanceOfTuples inspection.structuralTuples

/-- The proof-derived slice of an inspection. -/
@[expose] public def proved {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context} (inspection : Inspection meaning) :
    SemanticInstance context meaning.signature meaning.Carrier :=
  meaning.instanceOfTuples inspection.provedTuples

/-- Unified inspection soundness. Every output tuple came from one of the two
    supported sources, so local soundness for those sources proves soundness
    of the combined positive instance. -/
public theorem sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (inspection : Inspection meaning)
    (ground : World → GroundInstance meaning.signature meaning.Carrier)
    (structuralSound : Completes context inspection.rootStruct ground)
    (provedSound : Completes context inspection.proved ground) :
    Completes context inspection.data ground := by
  intro world compatible tuple present
  change tuple ∈ inspection.structuralTuples ++ inspection.provedTuples at present
  rcases List.mem_append.mp present with structural | proved
  · exact structuralSound world compatible tuple structural
  · exact provedSound world compatible tuple proved

/-- End-to-end soundness for the supported production origins. The two local
    realizations interpret the checked structural and `proved` origins of the
    same trace. No conclusion is drawn from missing tuples. -/
public theorem production_sound {World : Type u} {Root : Type v}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    (inspection : Inspection meaning)
    (knowledge : Iykyk.Metatheory.Knowledge World Root)
    (ground : World → GroundInstance meaning.signature meaning.Carrier)
    (trace : SpytialLean.TracedDataInstance)
    (checkedStructure : SpytialLean.CheckedStructuralTrace trace)
    (checkedProofs : SpytialLean.CheckedProofTrace trace)
    (required : StructuralRequirement
      (signature := meaning.signature)
      (Entry := (meaning.instanceOfTuples inspection.structuralTuples).Atom))
    (structural : ComputedStructuralCertificate trace inspection.rootStruct
      ground required checkedStructure)
    (proofs : ProductionProofRealization meaning knowledge ground
      inspection.provedTuples trace checkedProofs)
    (knowledgeSound : knowledge.Sound context) :
    Completes context inspection.data ground :=
  inspection.sound ground structural.adequate (proofs.sound knowledgeSound)

end Inspection

end SpytialLean.Metatheory

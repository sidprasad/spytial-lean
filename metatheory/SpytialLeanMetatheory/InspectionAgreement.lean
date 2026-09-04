module

public import SpytialLeanMetatheory.ProductionTraceInstance
public import SpytialLeanMetatheory.SemanticIsomorphism
public meta import SpytialLean.InContext

public section

/-!
# Agreement between proof-guided inspection and computation

An equality retained by IYKYK can expose a value that computation alone cannot
obtain from the selected term. The production inspector passes that value to
the ordinary structural walker before adding facts from the proof context.
This file gives those two phases a common semantics and proves that the source
of the knowledge does not change the resulting structural interface.
-/

namespace SpytialLean.Metatheory

open Lean

universe u v w x y

/-- Two relational descriptions have the same typed structure when they are
    isomorphic after generated atom names and tuple order are ignored. -/
public abbrev SameRelationalStructure {World : Type u} {SemanticType : Type v}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType} {Carrier : SemanticType → Type w}
    (left : SemanticInstance.{u, v, w, x} context signature Carrier)
    (right : SemanticInstance.{u, v, w, y} context signature Carrier) : Prop :=
  StructurallyAgrees left right

namespace RelationalInspection

/-- The semantic interpretation of one checked production inspection. The
    only run-specific evidence is the opaque result of `inspectKnownValue`;
    typing, proof checking, and definitional equality are interpreted once by
    `ProductionEvidenceMeaning`. -/
public structure KnownValue {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning.{u, v} World context) (knowledge : Iykyk.Afaik) where
  checked : SpytialLean.CheckedKnownValueInspection knowledge
  evidence : ProductionEvidenceMeaning meaning

namespace KnownValue

/-- Whether this inspection obtained its structural value by computation or proof. -/
public abbrev source {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :=
  known.checked.source

/-- The selected expression, checked at the equality's common type. -/
@[expose] public def rootTerm {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) : LeanExprMeaning.CheckedTerm meaning where
  expression := knowledge.root
  type := known.source.type
  checked := known.evidence.root_has_type known.source

/-- The actual refined expression checked at the type of the selected root. -/
@[expose] public def computedTerm {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) : LeanExprMeaning.CheckedTerm meaning where
  expression := known.checked.run.computedTerm
  type := known.source.type
  checked := known.evidence.result_has_type known.source

/-- The semantic inspection reconstructed from the actual production run.
    It includes every checked direct structural tuple and every checked proof
    tuple, including structure needed to display arguments of contextual
    facts. -/
@[expose] public def inspection {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) : Inspection meaning where
  structuralTuples :=
    structuralTraceTuples known.checked.run.structuralChecked known.evidence
  provedTuples := proofTraceTuples known.checked.run.proofsChecked known.evidence

/-- The root structure produced before the inspector adds contextual facts. -/
@[expose] public noncomputable def rootStructure {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :
    SemanticInstance context meaning.signature meaning.Carrier :=
  meaning.instanceOfTuples
    (structuralTraceTuples known.checked.run.computedChecked known.evidence)

/-- Ordinary semantic relationalization reconstructed from the actual checked
    computation phase retained by the production inspector. -/
@[expose] public noncomputable def computation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :
    SemanticInstance context meaning.signature meaning.Carrier :=
  known.rootStructure

/-- Computation or a retained equality identifies the inspected root with the
    expression represented by the production structural walk. -/
public theorem denotes_same_value {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) (world : World)
    (compatible : context world) :
    known.rootTerm.denote world compatible =
      known.computedTerm.denote world compatible := by
  simpa [rootTerm, computedTerm, LeanExprMeaning.CheckedTerm.denote] using
    known.evidence.checked_value_denotes_same known.source world compatible

/-- Every tuple reported by this actual rooted inspection is justified by its
    checked structural or proof origin. -/
public theorem sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :
    Completes context known.inspection.data (ProductionTupleHolds.ground meaning) :=
  known.inspection.sound (ProductionTupleHolds.ground meaning)
    (structuralTraceTuples_sound known.checked.run.structuralChecked known.evidence)
    (proofTraceTuples_sound known.checked.run.proofsChecked known.evidence)

end KnownValue

/-- The semantic content of knowledge-source independence. Computation or a
    checked equality identifies the two roots as values, while the relational
    isomorphism identifies the structure reported by the common root walk. -/
public structure KnowledgeSourceIndependent {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) : Prop where
  same_value : ∀ world (compatible : context world),
    known.rootTerm.denote world compatible =
      known.computedTerm.denote world compatible
  same_structure : SameRelationalStructure known.rootStructure known.computation

/-- **Knowledge-source independence.** Whether Lean obtains the walked value
    by computation or by a retained equality, the inspected term and computed
    expression denote the same value, and proof-guided inspection has exactly
    that computed root structure. This holds for the finite result actually
    produced; it does not require an unbounded walk. -/
public theorem knowledge_source_independence {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :
    KnowledgeSourceIndependent known where
  same_value := known.denotes_same_value
  same_structure := by
    exact ⟨SemanticIso.refl known.rootStructure⟩

/-- **Proof-guided inspection agrees with computation.** The actual checked
    result returned by `inspectKnownValue` has the same root value and the same
    finite structural relational instance as its retained computation phase.
    Proof-derived tuples may add facts, but they do not replace that common
    structural interface. -/
public theorem proof_guided_inspection_agrees_with_computation {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (checked : SpytialLean.CheckedKnownValueInspection knowledge)
    (evidence : ProductionEvidenceMeaning meaning) :
    KnowledgeSourceIndependent ({ checked, evidence } : KnownValue meaning knowledge) :=
  knowledge_source_independence { checked, evidence }

end RelationalInspection

end SpytialLean.Metatheory

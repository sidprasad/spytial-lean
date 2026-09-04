module

public import SpytialLeanMetatheory.ProductionTraceInstance
public import SpytialLeanMetatheory.FreshStructuralCorrespondence

public section

/-!
# Agreement between proof-guided inspection and fresh relationalization

An equality retained by IYKYK can expose a value that computation alone cannot
obtain from the selected term. The production inspector passes that value to
the ordinary structural walker before adding facts from the proof context.
This file gives those two phases a common semantics and proves that the source
of the knowledge does not change the resulting structural interface.
-/

namespace SpytialLean.Metatheory

open Lean SpytialLean

universe u v

namespace RelationalInspection

/-- The semantic interpretation of one checked production inspection. The
    fresh field is produced by rerunning the actual ordinary relationalizer
    on the value retained by `inspectKnownValue`. -/
public structure KnownValue {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    (meaning : LeanExprMeaning.{u, v} World context) (knowledge : Iykyk.Afaik) where
  production : CheckedFreshRelationalization knowledge
  evidence : ProductionEvidenceMeaning meaning

namespace KnownValue

/-- The checked proof-guided phase of the paired production run. -/
public abbrev checked {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) : CheckedKnownValueInspection knowledge :=
  known.production.inspection

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
    checked equality identifies the two roots as values, while a checked
    two-way correspondence relates the retained and fresh structural walks. -/
public structure KnowledgeSourceIndependent {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) : Prop where
  same_value : ∀ world (compatible : context world),
    known.rootTerm.denote world compatible =
      known.computedTerm.denote world compatible
  root_structure_retained : RootStructureRetained meaning
    known.checked.run.computedChecked known.checked.run.structuralChecked
  same_structure : SameProductionStructure meaning known.checked.run.computedChecked
    known.production.checked

/-- Whether Lean obtains the walked value by computation or by a retained
    equality, a fresh ordinary relationalization has the same typed relational
    structure as the root phase of proof-guided inspection. -/
public theorem knowledge_source_independence {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (known : KnownValue meaning knowledge) :
    KnowledgeSourceIndependent known where
  same_value := known.denotes_same_value
  root_structure_retained := inspection_retains_root_structure
    known.production known.evidence
  same_structure := fresh_relationalization_agrees_with_inspection_root
    known.production known.evidence

/-- **Proof-guided inspection agrees with fresh relationalization.** For every
    checked inspection and every successful fresh production rerun, Lean
    identifies the selected root with the walked value, retains that root
    structure in the completed inspection, and proves that a fresh structural
    trace has the same relation heads, rules, typed terms, and graph
    connectivity up to fresh atom names. -/
public theorem proof_guided_inspection_agrees_with_fresh_relationalization
    {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning.{u, v} World context} {knowledge : Iykyk.Afaik}
    (production : CheckedFreshRelationalization knowledge)
    (evidence : ProductionEvidenceMeaning meaning) :
    KnowledgeSourceIndependent
      ({ production, evidence } : KnownValue meaning knowledge) :=
  knowledge_source_independence { production, evidence }

end RelationalInspection

end SpytialLean.Metatheory

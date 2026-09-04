module

public import SpytialLeanMetatheory.Inspection

public section

/-!
# Semantic instances constructed from checked production traces

This file maps every checked structural and proof origin in a production
trace to the shared Lean-backed relation semantics. Custom, observed,
tabulated, symbolic, and synthetic origins remain outside this core claim.
-/

namespace SpytialLean.Metatheory

open Lean SpytialLean

universe u v

/-- All typed tuples reconstructed from the checked proof origins of a trace. -/
@[expose] public def proofTraceTuples {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedProofTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    List (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) :=
  checked.origins.toList.map fun origin => provedOriginTuple evidence origin

/-- Checked proof origins are sound in the independent Lean-backed ground. -/
public theorem proofTraceTuples_sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedProofTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    Completes context (meaning.instanceOfTuples (proofTraceTuples checked evidence))
      (ProductionTupleHolds.ground meaning) := by
  intro world compatible tuple present
  obtain ⟨origin, _, rfl⟩ := List.mem_map.mp present
  exact ProductionTupleHolds.checkedProvedTupleHolds evidence
    (provedOriginTuple_realizes evidence origin) world compatible

/-- All typed tuples reconstructed from checked structural origins of a trace. -/
@[expose] public def structuralTraceTuples {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedStructuralTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    List (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) :=
  checked.origins.toList.map fun origin => structuralOriginTuple evidence origin

/-- Checked constructor and projection origins are sound in the independent ground. -/
public theorem structuralTraceTuples_sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedStructuralTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    Completes context (meaning.instanceOfTuples (structuralTraceTuples checked evidence))
      (ProductionTupleHolds.ground meaning) := by
  intro world compatible tuple present
  obtain ⟨origin, _, rfl⟩ := List.mem_map.mp present
  exact ProductionTupleHolds.structuralTupleHolds evidence
    (structuralOriginTuple_realizes evidence origin) world compatible

/-- The two checked built-in origin classes for one production trace. -/
public structure CheckedCoreTrace (trace : TracedDataInstance) where
  structural : CheckedStructuralTrace trace
  proofs : CheckedProofTrace trace

namespace CheckedCoreTrace

/-- Run both production checkers and retain the checked built-in origins. -/
public meta def check (cfg : WalkConfig) (trace : TracedDataInstance)
    (provenance : Provenance) (selectorEvidence : SelectorEvidence) :
    MetaM (CheckedCoreTrace trace) := do
  return {
    structural := ← checkStructuralTrace cfg trace provenance selectorEvidence
    proofs := ← checkProofTrace trace selectorEvidence }

/-- The unified semantic inspection constructed from a checked core trace. -/
@[expose] public def inspection {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedCoreTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) : Inspection meaning where
  structuralTuples := structuralTraceTuples checked.structural evidence
  provedTuples := proofTraceTuples checked.proofs evidence

/-- Every supported tuple reconstructed from a checked production trace is
    true in the independent Lean-backed ground. -/
public theorem inspection_sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedCoreTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) :
    Completes context (checked.inspection evidence).data
      (ProductionTupleHolds.ground meaning) :=
  (checked.inspection evidence).sound (ProductionTupleHolds.ground meaning)
    (structuralTraceTuples_sound checked.structural evidence)
    (proofTraceTuples_sound checked.proofs evidence)

end CheckedCoreTrace

end SpytialLean.Metatheory

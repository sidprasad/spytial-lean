module

public import SpytialLeanMetatheory.RelationalInstance
public meta import SpytialLean.InContext

public section

/-!
# Production correspondence

These theorems connect the formalization to both production relationalizers.
They prove that removing trace evidence gives exactly the existing public
output. They do not prove that a tuple is true; that proof depends on the
tuple's origin.
-/

namespace SpytialLean.Metatheory

open Lean SpytialLean

/-- The atoms interpreted by the semantics are exactly the atoms accumulated
    by the production walk; `toDataInstance` does not reconstruct them. -/
theorem production_atoms_are_preserved (state : WalkState) :
    state.toDataInstance.atoms = state.atoms :=
  rfl

/-- Building the production trace changes no JSON data. -/
theorem production_trace_erases_to_data (state : WalkState) :
    state.toTracedDataInstance.data = state.toDataInstance :=
  rfl

/-- The computed-value evidence API is the traced producer followed by
    tuple-origin erasure. -/
theorem computed_evidence_is_trace_erasure (e : Expr) (cfg : WalkConfig := {})
    (observations : Array Expr := #[]) :
    relationalizeWithEvidence e cfg observations = do
      let (trace, provenance, evidence) ← relationalizeWithTrace e cfg observations
      return (trace.data, provenance, evidence) := by
  exact relationalizeWithEvidence_eq_trace_erasure e cfg observations

/-- The public production entry point is definitionally the evidence-producing
    walk followed by evidence erasure. This is the initial runtime boundary;
    it becomes useful for soundness once the evidence is indexed by emissions. -/
theorem production_output_is_evidence_erasure (e : Expr) (cfg : WalkConfig := {})
    (observations : Array Expr := #[]) :
    relationalize e cfg observations = do
      let (data, _, _) ← relationalizeWithEvidence e cfg observations
      return data := by
  rfl

/-- The proof-context producer has the same boundary: its public data-only
    entry point is exactly its evidence-producing run followed by erasure. -/
theorem proof_context_output_is_evidence_erasure (afaik : Iykyk.Afaik)
    (cfg : WalkConfig := {}) (observations : Array Expr := #[]) :
    relationalizeAfaik afaik cfg observations = do
      let (data, _, _, _, _) ← relationalizeAfaikWithEvidence afaik cfg observations
      return data := by
  exact relationalizeAfaik_eq_evidence_erasure afaik cfg observations

/-- The proof-context evidence API is likewise the traced producer followed by
    tuple-origin erasure. -/
theorem proof_context_evidence_is_trace_erasure (afaik : Iykyk.Afaik)
    (cfg : WalkConfig := {}) (observations : Array Expr := #[]) :
    relationalizeAfaikWithEvidence afaik cfg observations = do
      let (trace, provenance, datum, inspection, evidence) ←
        relationalizeAfaikWithTrace afaik cfg observations
      return (trace.data, provenance, datum, inspection, evidence) := by
  exact relationalizeAfaikWithEvidence_eq_trace_erasure afaik cfg observations

/-- The checked two-phase run changes no production output. Erasing its
    retained computation phase gives the established proof-context trace API. -/
theorem proof_context_trace_is_phase_erasure (afaik : Iykyk.Afaik)
    (cfg : WalkConfig := {}) (observations : Array Expr := #[]) :
    relationalizeAfaikWithTrace afaik cfg observations = do
      let result ← relationalizeAfaikWithPhaseTrace afaik cfg observations
      return (result.trace, result.provenance, result.datum, result.inspection,
        result.evidence) := by
  exact relationalizeAfaikWithTrace_eq_phase_erasure afaik cfg observations

end SpytialLean.Metatheory

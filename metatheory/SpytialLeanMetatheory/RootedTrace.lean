module

public import SpytialLeanMetatheory.ProductionTraceInstance

public section

/-!
# The root structural slice of a production trace

The contextual producer walks the selected root before it adds unrelated
facts. No phase marker is needed to recover that structure: start at the root
atom and follow checked constructor-field and projection edges in their
source-to-child direction.
-/

namespace SpytialLean.Metatheory

open SpytialLean

universe u

/-- Atom reachability through checked structural origins. Predicate and
    function-graph tuples are deliberately not traversal edges. -/
public inductive RootReachable (trace : TracedDataInstance)
    (checked : CheckedStructuralTrace trace) (root : String) : String → Prop where
  | root : RootReachable trace checked root root
  | child (origin : CheckedStructuralOrigin)
      (originChecked : origin ∈ checked.origins.toList)
      (originEmitted : origin.emission ∈ trace.emissions)
      (sourceReachable : RootReachable trace checked root origin.sourceAtom) :
      RootReachable trace checked root origin.childAtom

/-- A checked structural origin belongs to the root slice when its source is
    reachable from the selected root atom. -/
public def IsRootStructuralOrigin (trace : TracedDataInstance)
    (checked : CheckedStructuralTrace trace) (root : String)
    (origin : CheckedStructuralOrigin) : Prop :=
  origin ∈ checked.origins.toList ∧
    origin.emission ∈ trace.emissions ∧
      RootReachable trace checked root origin.sourceAtom

/-- Positive tuple membership in `rootStruct` at the production wire
    boundary. The semantic layer later replaces string IDs and type labels
    with typed, denoting atoms. -/
public def RootStructHasTuple (trace : TracedDataInstance)
    (checked : CheckedStructuralTrace trace) (root relation : String)
    (types atoms : Array String) : Prop :=
  ∃ origin, IsRootStructuralOrigin trace checked root origin ∧
    Describes origin.emission relation types atoms

/-- Root extraction introduces no tuple. Every rooted structural tuple is an
    actual tuple of the production JSON instance. -/
public theorem rootStruct_subset_output (trace : TracedDataInstance)
    (checked : CheckedStructuralTrace trace) (root relation : String)
    (types atoms : Array String) (valid : trace.wellFormedTrace = true)
    (present : RootStructHasTuple trace checked root relation types atoms) :
    HasTuple trace.data relation types atoms := by
  obtain ⟨origin, ⟨_, emitted, _⟩, relationEq, atomsEq, typesEq⟩ := present
  simp only [TracedDataInstance.wellFormedTrace, Bool.and_eq_true] at valid
  have output := noSpuriousOrigins_of_originsMatchOutput trace valid.1.1.2
    origin.emission emitted
  simpa only [relationEq, atomsEq, typesEq] using output

/-- Following a rooted structural edge keeps the child in the root slice. -/
public theorem child_reachable (trace : TracedDataInstance)
    (checked : CheckedStructuralTrace trace) (root : String)
    (origin : CheckedStructuralOrigin)
    (belongs : IsRootStructuralOrigin trace checked root origin) :
    RootReachable trace checked root origin.childAtom :=
  .child origin belongs.1 belongs.2.1 belongs.2.2

/-- The checked structural origins reachable from the inspected root. This is
    a semantic projection of the existing trace; it does not run the
    relationalizer again. -/
@[expose] public noncomputable def rootedStructuralOrigins
    (trace : TracedDataInstance) (checked : CheckedStructuralTrace trace)
    (root : String) : List CheckedStructuralOrigin := by
  classical
  exact checked.origins.toList.filter fun origin =>
    decide (IsRootStructuralOrigin trace checked root origin)

/-- Every origin selected for the rooted projection was checked by the
    production structural checker. -/
public theorem mem_checked_of_mem_rootedStructuralOrigins
    (trace : TracedDataInstance) (checked : CheckedStructuralTrace trace)
    (root : String) (origin : CheckedStructuralOrigin)
    (present : origin ∈ rootedStructuralOrigins trace checked root) :
    origin ∈ checked.origins.toList := by
  classical
  exact (List.mem_filter.mp present).1

/-- Interpret the actual root-reachable structural origins as typed semantic
    tuples. Generated JSON atom identifiers remain attached to the expression
    atoms, but only origins belonging to the selected root are included. -/
@[expose] public noncomputable def rootedStructuralTuples {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedStructuralTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) (root : String) :
    List (RelationalTuple meaning.signature (LeanExprMeaning.ExprAtom meaning)) :=
  (rootedStructuralOrigins trace checked root).map fun origin =>
    structuralOriginTuple evidence origin

/-- Root projection preserves structural soundness: every selected tuple came
    from a checked structural origin in the production trace. -/
public theorem rootedStructuralTuples_sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedStructuralTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) (root : String) :
    Completes context (meaning.instanceOfTuples
      (rootedStructuralTuples checked evidence root))
      (ProductionTupleHolds.ground meaning) := by
  intro world compatible tuple present
  obtain ⟨origin, _, rfl⟩ := List.mem_map.mp present
  exact ProductionTupleHolds.structuralTupleHolds evidence
    (structuralOriginTuple_realizes evidence origin) world compatible

namespace CheckedCoreTrace

/-- The semantic inspection represented by an actual checked production trace
    at one selected root. Structural tuples are restricted to the root walk;
    proof-derived tuples remain available as contextual refinements. -/
@[expose] public noncomputable def rootedInspection {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedCoreTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) (root : String) : Inspection meaning where
  structuralTuples := rootedStructuralTuples checked.structural evidence root
  provedTuples := proofTraceTuples checked.proofs evidence

/-- The actual rooted inspection is sound in the same production semantics as
    the complete checked trace. -/
public theorem rootedInspection_sound {World : Type u}
    {context : Iykyk.Metatheory.Context World}
    {meaning : LeanExprMeaning World context}
    {trace : TracedDataInstance} (checked : CheckedCoreTrace trace)
    (evidence : ProductionEvidenceMeaning meaning) (root : String) :
    Completes context (checked.rootedInspection evidence root).data
      (ProductionTupleHolds.ground meaning) :=
  (checked.rootedInspection evidence root).sound
    (ProductionTupleHolds.ground meaning)
    (rootedStructuralTuples_sound checked.structural evidence root)
    (proofTraceTuples_sound checked.proofs evidence)

end CheckedCoreTrace

end SpytialLean.Metatheory

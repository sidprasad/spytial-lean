module

public import SpytialLeanMetatheory.RelationalInstance
public meta import SpytialLean.Relationalizer

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

end SpytialLean.Metatheory

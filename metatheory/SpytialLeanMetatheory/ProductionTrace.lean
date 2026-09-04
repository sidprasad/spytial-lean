module

public import SpytialLean.Types

public section

/-!
# Connection to production traces

The production walkers retain an origin for every emitted tuple and erase
those origins before returning the existing JSON format. This file proves the
small structural fact needed by the paper: a trace accepted by the executable
checker accounts for exactly the tuples in the real output.

It does not assign semantics to arbitrary Lean expressions or custom
relationalizers.
-/

namespace SpytialLean.Metatheory

open SpytialLean

/-- The production JSON contains the named typed tuple. -/
public def HasTuple (data : JsonDataInstance) (relation : String)
    (types atoms : Array String) : Prop :=
  ∃ rel ∈ data.relations,
    rel.name = relation ∧
      ∃ tuple ∈ rel.tuples, tuple.atoms = atoms ∧ tuple.types = types

/-- A traced emission describes the named typed tuple. -/
public def Describes (emission : TupleEmission) (relation : String)
    (types atoms : Array String) : Prop :=
  emission.relation = relation ∧ emission.tuple.atoms = atoms ∧
    emission.tuple.types = types

/-- At least one production origin is associated with a tuple. -/
public def HasOrigin (trace : TracedDataInstance) (relation : String)
    (types atoms : Array String) : Prop :=
  ∃ emission ∈ trace.emissions, Describes emission relation types atoms

/-- Every positive output tuple has a production origin. -/
public def OriginsCover (trace : TracedDataInstance) : Prop :=
  ∀ {relation types atoms}, HasTuple trace.data relation types atoms →
    HasOrigin trace relation types atoms

/-- Every recorded origin describes a tuple in the erased output. -/
public def NoSpuriousOrigins (trace : TracedDataInstance) : Prop :=
  ∀ emission ∈ trace.emissions,
    HasTuple trace.data emission.relation emission.tuple.types emission.tuple.atoms

/-- Output tuples and their recorded origins account for one another exactly. -/
public def OriginsExact (trace : TracedDataInstance) : Prop :=
  OriginsCover trace ∧ NoSpuriousOrigins trace

/-- The executable coverage check implies propositional origin coverage. -/
public theorem originsCover_of_coversOutput (trace : TracedDataInstance)
    (covered : trace.coversOutput = true) : OriginsCover trace := by
  intro relation types atoms present
  rcases present with
    ⟨relationData, relationMem, relationName,
      tuple, tupleMem, tupleAtoms, tupleTypes⟩
  simp only [TracedDataInstance.coversOutput,
    Array.all_eq_true_iff_forall_mem] at covered
  have relationCovered := covered relationData relationMem
  have tupleCovered := relationCovered tuple tupleMem
  rw [Array.any_eq_true] at tupleCovered
  rcases tupleCovered with ⟨index, inBounds, matching⟩
  let emission := trace.emissions[index]
  refine ⟨emission, Array.getElem_mem inBounds, ?_⟩
  simp only [TupleEmission.matches, Bool.and_eq_true, beq_iff_eq] at matching
  rcases matching with
    ⟨⟨emissionRelation, emissionAtoms⟩, emissionTupleTypes⟩
  exact ⟨emissionRelation.trans relationName, emissionAtoms.trans tupleAtoms,
    emissionTupleTypes.trans tupleTypes⟩

/-- The reverse executable check rules out origins for absent tuples. -/
public theorem noSpuriousOrigins_of_originsMatchOutput (trace : TracedDataInstance)
    (checked : trace.originsMatchOutput = true) : NoSpuriousOrigins trace := by
  intro emission emissionMem
  simp only [TracedDataInstance.originsMatchOutput,
    Array.all_eq_true_iff_forall_mem] at checked
  have relationPresent := checked emission emissionMem
  rw [Array.any_eq_true] at relationPresent
  rcases relationPresent with ⟨relationIndex, relationBounds, tuplePresent⟩
  let relation := trace.data.relations[relationIndex]
  rw [Array.any_eq_true] at tuplePresent
  rcases tuplePresent with ⟨tupleIndex, tupleBounds, matching⟩
  let tuple := relation.tuples[tupleIndex]
  simp only [TupleEmission.matches, Bool.and_eq_true, beq_iff_eq] at matching
  rcases matching with ⟨⟨relationName, tupleAtoms⟩, tupleTypes⟩
  exact ⟨relation, Array.getElem_mem relationBounds, relationName.symm,
    tuple, Array.getElem_mem tupleBounds, tupleAtoms.symm, tupleTypes.symm⟩

/-- A well-formed production trace accounts exactly for the JSON tuples that
    users and Spytial receive. -/
public theorem originsExact_of_wellFormedTrace (trace : TracedDataInstance)
    (valid : trace.wellFormedTrace = true) : OriginsExact trace := by
  simp only [TracedDataInstance.wellFormedTrace, Bool.and_eq_true] at valid
  exact ⟨originsCover_of_coversOutput trace valid.1.1.1,
    noSpuriousOrigins_of_originsMatchOutput trace valid.1.1.2⟩

end SpytialLean.Metatheory

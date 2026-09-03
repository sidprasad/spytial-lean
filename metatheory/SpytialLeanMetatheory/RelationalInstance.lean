module

public import SpytialLean.Types

public section

/-!
# Wire-level partial relational instances

This module gives an open-world positive-information order directly to the
`JsonDataInstance` type emitted by the production Spytial Lean relationalizer.
It deliberately ignores labels, relation ordering, and fresh atom names. Since
raw JSON does not retain Lean denotations or tuple origins, this is the
wire-level skeleton of the eventual semantic completion relation, not yet a
claim that an emitted tuple is true of the inspected value. Production traces
now retain origins; the remaining correspondence is to validate the semantic
claim associated with each origin.
-/

namespace SpytialLean.Metatheory

open SpytialLean

/-- The instance contains an atom with the given identifier and type. Labels
    are presentational and therefore absent from this predicate. -/
def HasAtom (data : JsonDataInstance) (id type : String) : Prop :=
  ∃ atom ∈ data.atoms, atom.id = id ∧ atom.type = type

/-- The instance contains the typed tuple in the named relation. Relation IDs
    are serialization details; semantic lookup uses the relation name and the
    tuple-local types. `JsonRelation.types` is only default/display metadata. -/
def HasTuple (data : JsonDataInstance) (relation : String)
    (types atoms : Array String) : Prop :=
  ∃ rel ∈ data.relations,
    rel.name = relation ∧
      ∃ tuple ∈ rel.tuples, tuple.atoms = atoms ∧ tuple.types = types

/-- A traced emission describes the named typed tuple. -/
def Describes (emission : TupleEmission) (relation : String)
    (types atoms : Array String) : Prop :=
  emission.relation = relation ∧ emission.tuple.atoms = atoms ∧
    emission.tuple.types = types

/-- At least one production origin is associated with the tuple. -/
def HasOrigin (trace : TracedDataInstance) (relation : String)
    (types atoms : Array String) : Prop :=
  ∃ emission ∈ trace.emissions, Describes emission relation types atoms

/-- Every positive output tuple has a production origin. -/
def OriginsCover (trace : TracedDataInstance) : Prop :=
  ∀ {relation types atoms}, HasTuple trace.data relation types atoms →
    HasOrigin trace relation types atoms

/-- Every recorded origin describes a tuple that actually appears in the
    erased output. -/
def NoSpuriousOrigins (trace : TracedDataInstance) : Prop :=
  ∀ emission ∈ trace.emissions,
    HasTuple trace.data emission.relation emission.tuple.types emission.tuple.atoms

/-- The output tuples and recorded origins account for one another exactly.
    Multiple independent origins for one tuple are permitted. -/
def OriginsExact (trace : TracedDataInstance) : Prop :=
  OriginsCover trace ∧ NoSpuriousOrigins trace

/-- The executable coverage check implies the propositional metatheory
    invariant. This concerns trace structure, not yet origin semantics. -/
theorem originsCover_of_coversOutput (trace : TracedDataInstance)
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

/-- The reverse executable check rules out origins for tuples absent from the
    output. -/
theorem noSpuriousOrigins_of_originsMatchOutput (trace : TracedDataInstance)
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

/-- The full executable trace check used by both production entry points is
    strong enough to establish metatheoretic origin coverage. -/
theorem originsCover_of_wellFormedTrace (trace : TracedDataInstance)
    (valid : trace.wellFormedTrace = true) : OriginsCover trace := by
  apply originsCover_of_coversOutput trace
  simp only [TracedDataInstance.wellFormedTrace, Bool.and_eq_true] at valid
  exact valid.1.1.1

/-- The complete executable check establishes exact correspondence between
    positive output tuples and their recorded origins. -/
theorem originsExact_of_wellFormedTrace (trace : TracedDataInstance)
    (valid : trace.wellFormedTrace = true) : OriginsExact trace := by
  simp only [TracedDataInstance.wellFormedTrace, Bool.and_eq_true] at valid
  exact ⟨originsCover_of_coversOutput trace valid.1.1.1,
    noSpuriousOrigins_of_originsMatchOutput trace valid.1.1.2⟩

/-- A homomorphism of the serialized relational data. It maps atom identifiers
    while preserving atom and tuple type labels and every positive source
    tuple. Semantic Lean typing and denotation are deliberately not claimed. -/
structure WireHom (source target : JsonDataInstance) where
  atom : String → String
  mapsAtom : ∀ {id type}, HasAtom source id type → HasAtom target (atom id) type
  mapsTuple : ∀ {relation types atoms}, HasTuple source relation types atoms →
    HasTuple target relation types (atoms.map atom)

/-- `target` wire-completes the positive information in `source`. -/
def WireCompletes (source target : JsonDataInstance) : Prop :=
  Nonempty (WireHom source target)

/-- The set of all open-world completions of an instance. -/
def wireCompletions (source : JsonDataInstance) : JsonDataInstance → Prop :=
  WireCompletes source

/-- Every instance completes itself. -/
def WireHom.refl (data : JsonDataInstance) : WireHom data data where
  atom := id
  mapsAtom := by simp
  mapsTuple := by simp

/-- Relational homomorphisms compose. -/
def WireHom.comp {first second third : JsonDataInstance}
    (right : WireHom second third) (left : WireHom first second) : WireHom first third where
  atom := right.atom ∘ left.atom
  mapsAtom present := right.mapsAtom (left.mapsAtom present)
  mapsTuple present := by
    simpa [Function.comp_def, Array.map_map] using
      right.mapsTuple (left.mapsTuple present)

theorem wireCompletes_refl (data : JsonDataInstance) : WireCompletes data data :=
  ⟨WireHom.refl data⟩

theorem wireCompletes_trans {first second third : JsonDataInstance}
    (left : WireCompletes first second) (right : WireCompletes second third) :
    WireCompletes first third := by
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨right.comp left⟩

/-- Adding information to a completion does not invalidate the original
    positive instance. This is the basic open-world monotonicity law. -/
theorem wireCompletion_upward_closed {source ground extended : JsonDataInstance}
    (groundCompletes : WireCompletes source ground)
    (extendedCompletes : WireCompletes ground extended) :
    WireCompletes source extended :=
  wireCompletes_trans groundCompletes extendedCompletes

/-! ## A concrete open-world counterexample

The following two ground candidates both complete an instance with one vertex
and an empty `edge` table. One candidate contains a self-edge and the other does
not. Hence absence from the partial table cannot be interpreted as negation.
-/

def openWorldVertex : JsonAtom :=
  { id := "x", type := "Vertex", label := "x" }

def openWorldEdgeTypes : Array String := #["Vertex", "Vertex"]

def openWorldSelfEdge : JsonTuple :=
  { atoms := #["x", "x"], types := openWorldEdgeTypes }

def openWorldEdgeRelation (tuples : Array JsonTuple) : JsonRelation :=
  { id := "edge", name := "edge", types := openWorldEdgeTypes, tuples }

def openWorldWithoutEdge : JsonDataInstance :=
  { atoms := #[openWorldVertex], relations := #[openWorldEdgeRelation #[]] }

def openWorldWithEdge : JsonDataInstance :=
  { atoms := #[openWorldVertex], relations := #[openWorldEdgeRelation #[openWorldSelfEdge]] }

def openWorldAddSelfEdge : WireHom openWorldWithoutEdge openWorldWithEdge where
  atom := id
  mapsAtom := by
    intro id type present
    simpa [HasAtom, openWorldWithoutEdge, openWorldWithEdge] using present
  mapsTuple := by
    intro relation types atoms present
    simp [HasTuple, openWorldWithoutEdge, openWorldEdgeRelation] at present

/-- One positive partial instance has completions that disagree on an absent
    tuple. `HasTuple` failure therefore carries no negative proposition. -/
theorem absent_tuple_is_unknown :
    ¬HasTuple openWorldWithoutEdge "edge" openWorldEdgeTypes #["x", "x"] ∧
      HasTuple openWorldWithEdge "edge" openWorldEdgeTypes #["x", "x"] ∧
      WireCompletes openWorldWithoutEdge openWorldWithoutEdge ∧
        WireCompletes openWorldWithoutEdge openWorldWithEdge := by
  refine ⟨?_, ?_, wireCompletes_refl openWorldWithoutEdge, ⟨openWorldAddSelfEdge⟩⟩
  · simp [HasTuple, openWorldWithoutEdge, openWorldEdgeRelation]
  · simp [HasTuple, openWorldWithEdge, openWorldEdgeRelation, openWorldSelfEdge,
      openWorldEdgeTypes]

end SpytialLean.Metatheory

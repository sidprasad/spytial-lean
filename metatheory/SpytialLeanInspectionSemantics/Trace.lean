module

public import SpytialLeanInspectionSemantics.Structural

public section

/-!
# Traces: instances that remember where each tuple came from

A trace is a relational instance together with a finite tuple set and an origin relation. A tuple
occurs once even when several sources justify it; the origin relation retains all of those sources.
An origin does not change what a tuple means, so a trace is sound exactly when the instance
obtained by erasing its origins is sound. The structural walk of an exposed representation is
tagged with whether the exposure came from evaluation or from a checked proof.
-/

namespace SpytialLean.Semantics

universe u v w

/-- How a constructor-headed representation of a term was obtained. -/
public inductive Exposure where
  | evaluation
  | proof
  deriving DecidableEq

/-- Where a reported tuple came from. -/
public inductive Origin where
  | structural (exposure : Exposure)
  | knowledge
  deriving DecidableEq

/-- A finite positive relational instance whose unique tuples remember every origin. -/
public structure Trace {World : Type u} {Ty : Type v} (context : Iykyk.Metatheory.Context World)
    {signature : Signature Ty} (model : Model World signature) where
  atoms : FiniteSet (TypedAtom (Atom context model))
  tuples : FiniteSet (Tuple signature (Atom context model))
  origins : Tuple signature (Atom context model) → Origin → Prop
  tuplesHaveOrigins : ∀ tuple, tuple ∈ tuples ↔ ∃ origin, origins tuple origin
  tuplesUseAtoms : ∀ tuple, tuple ∈ tuples → ∀ atom, atom ∈ tuple.atoms → atom ∈ atoms

namespace Trace

variable {World : Type u} {Ty : Type v} {context : Iykyk.Metatheory.Context World}
  {signature : Signature Ty} {model : Model World signature}

/-- The trace with no atoms, tuples, or origins. -/
@[expose] public def empty : Trace context model where
  atoms := .empty
  tuples := .empty
  origins := fun _ _ => False
  tuplesHaveOrigins := by simp [FiniteSet.mem_empty]
  tuplesUseAtoms := by
    intro tuple present
    exact False.elim present

/-- A trace containing one atom and no relational claims. -/
@[expose] public def ofAtom {sort : Ty} (atom : Atom context model sort) : Trace context model where
  atoms := .singleton ⟨sort, atom⟩
  tuples := .empty
  origins := fun _ _ => False
  tuplesHaveOrigins := by simp [FiniteSet.mem_empty]
  tuplesUseAtoms := by
    intro tuple present
    exact False.elim present

/-- A trace containing one tuple with the given origin and exactly the atoms it uses. -/
@[expose] public def ofTuple (origin : Origin) (tuple : Tuple signature (Atom context model)) :
    Trace context model where
  atoms := .ofList tuple.atoms
  tuples := .singleton tuple
  origins := fun candidate source => candidate = tuple ∧ source = origin
  tuplesHaveOrigins := by
    intro candidate
    constructor
    · intro present
      exact ⟨origin, present, rfl⟩
    · rintro ⟨source, present, _⟩
      exact present
  tuplesUseAtoms := by
    intro candidate present atom atomPresent
    simp only [FiniteSet.mem_singleton] at present
    subst candidate
    exact atomPresent

/-- Combine independently obtained traces. Atoms and tuples are set unions; origins are retained
pointwise, so equal tuples remain one row with several possible justifications. -/
@[expose] public def union (left right : Trace context model) : Trace context model where
  atoms := left.atoms.union right.atoms
  tuples := left.tuples.union right.tuples
  origins := fun tuple origin => left.origins tuple origin ∨ right.origins tuple origin
  tuplesHaveOrigins := by
    intro tuple
    constructor
    · rintro (present | present)
      · obtain ⟨origin, justified⟩ := (left.tuplesHaveOrigins tuple).mp present
        exact ⟨origin, Or.inl justified⟩
      · obtain ⟨origin, justified⟩ := (right.tuplesHaveOrigins tuple).mp present
        exact ⟨origin, Or.inr justified⟩
    · rintro ⟨origin, justified | justified⟩
      · exact Or.inl ((left.tuplesHaveOrigins tuple).mpr ⟨origin, justified⟩)
      · exact Or.inr ((right.tuplesHaveOrigins tuple).mpr ⟨origin, justified⟩)
  tuplesUseAtoms := by
    intro tuple present atom atomPresent
    rcases present with fromLeft | fromRight
    · exact Or.inl (left.tuplesUseAtoms tuple fromLeft atom atomPresent)
    · exact Or.inr (right.tuplesUseAtoms tuple fromRight atom atomPresent)

/-- Forget every origin. This is the instance consumed by presentation. -/
@[expose] public def erase (trace : Trace context model) : Instance context model where
  atoms := trace.atoms
  tuples := trace.tuples
  tuplesUseAtoms := trace.tuplesUseAtoms

/-- Every tuple of a trace is true in every world allowed by the context. -/
@[expose] public def Sound (trace : Trace context model) : Prop :=
  ∀ tuple, tuple ∈ trace.tuples → ∀ world (compatible : context world),
    tuple.Holds world compatible

/-- The singleton trace records exactly its supplied origin. -/
public theorem origin_ofTuple (origin source : Origin)
    (tuple : Tuple signature (Atom context model)) :
    (ofTuple origin tuple).origins tuple source ↔ source = origin := by
  simp [ofTuple]

/-- Trace union retains an origin from either input without duplicating the tuple. -/
public theorem origin_union (left right : Trace context model)
    (tuple : Tuple signature (Atom context model)) (origin : Origin) :
    (left.union right).origins tuple origin ↔
      left.origins tuple origin ∨ right.origins tuple origin := by
  rfl

/-- `larger` retains every atom, tuple, and origin reported by `smaller`. -/
public structure ContainedIn (smaller larger : Trace context model) : Prop where
  atoms : ∀ atom, atom ∈ smaller.atoms → atom ∈ larger.atoms
  tuples : ∀ tuple, tuple ∈ smaller.tuples → tuple ∈ larger.tuples
  origins : ∀ tuple origin, smaller.origins tuple origin → larger.origins tuple origin

public theorem ContainedIn.refl (trace : Trace context model) : trace.ContainedIn trace where
  atoms _ present := present
  tuples _ present := present
  origins _ _ present := present

public theorem ContainedIn.trans {first second third : Trace context model}
    (firstSecond : first.ContainedIn second) (secondThird : second.ContainedIn third) :
    first.ContainedIn third where
  atoms atom present := secondThird.atoms atom (firstSecond.atoms atom present)
  tuples tuple present := secondThird.tuples tuple (firstSecond.tuples tuple present)
  origins tuple origin present := secondThird.origins tuple origin
    (firstSecond.origins tuple origin present)

public theorem containedIn_union_left (left right : Trace context model) :
    left.ContainedIn (left.union right) where
  atoms _ present := Or.inl present
  tuples _ present := Or.inl present
  origins _ _ present := Or.inl present

public theorem containedIn_union_right (left right : Trace context model) :
    right.ContainedIn (left.union right) where
  atoms _ present := Or.inr present
  tuples _ present := Or.inr present
  origins _ _ present := Or.inr present

/-- Combine a finite list of traces using deduplicating union. -/
@[expose] public def unions : List (Trace context model) → Trace context model
  | [] => empty
  | first :: rest => first.union (unions rest)

/-- Every member of a trace list is retained by their combined trace. -/
public theorem containedIn_unions_of_mem {candidate : Trace context model} :
    ∀ {traces : List (Trace context model)}, candidate ∈ traces →
      candidate.ContainedIn (unions traces)
  | [], present => by simp at present
  | first :: rest, present => by
      rcases List.mem_cons.mp present with equal | present
      · subst candidate
        exact containedIn_union_left first (unions rest)
      · exact (containedIn_unions_of_mem present).trans
          (containedIn_union_right first (unions rest))

/-- Trace containment survives erasing origins. -/
public theorem erase_containedIn {smaller larger : Trace context model}
    (contained : smaller.ContainedIn larger) :
    Instance.ContainedIn smaller.erase larger.erase where
  atoms := contained.atoms
  tuples := contained.tuples

public theorem erase_ofAtom {sort : Ty} (atom : Atom context model sort) :
    (ofAtom atom).erase = Instance.ofAtom atom := rfl

public theorem erase_ofTuple (origin : Origin) (tuple : Tuple signature (Atom context model)) :
    (ofTuple origin tuple).erase = Instance.ofTuple tuple := rfl

public theorem erase_union (left right : Trace context model) :
    (left.union right).erase = left.erase.union right.erase := by
  rfl

/-- Presentation erasure of a repeated trace is idempotent: no atom or tuple is duplicated. -/
public theorem erase_union_self (trace : Trace context model) :
    (trace.union trace).erase = trace.erase := by
  rw [erase_union, Instance.union_self]

/-- Repeating a contribution does not create a second origin entry either. -/
public theorem origin_union_self (trace : Trace context model)
    (tuple : Tuple signature (Atom context model)) (origin : Origin) :
    (trace.union trace).origins tuple origin ↔ trace.origins tuple origin := by
  simp [origin_union]

/-- When two sources justify one tuple, presentation still sees one row and the trace retains both
origins. -/
public theorem same_tuple_keeps_both_origins (first second : Origin)
    (tuple : Tuple signature (Atom context model)) :
    let combined := (ofTuple first tuple).union (ofTuple second tuple)
    tuple ∈ combined.tuples ∧ combined.origins tuple first ∧
      combined.origins tuple second ∧ combined.erase = Instance.ofTuple tuple := by
  refine ⟨Or.inl rfl, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, ?_⟩
  rw [erase_union, erase_ofTuple, erase_ofTuple, Instance.ofTuple_union_self]

/-- A trace is sound exactly when its erasure is sound. -/
public theorem sound_iff_erase (trace : Trace context model) :
    trace.Sound ↔ trace.erase.Sound := by rfl

/-- An atom alone makes no relational claim. -/
public theorem sound_ofAtom {sort : Ty} (atom : Atom context model sort) : (ofAtom atom).Sound := by
  intro tuple present
  exact False.elim present

/-- A singleton trace is sound exactly when its tuple holds; the origin is irrelevant. -/
public theorem sound_ofTuple (origin : Origin) (tuple : Tuple signature (Atom context model))
    (holds : ∀ world (compatible : context world), tuple.Holds world compatible) :
    (ofTuple origin tuple).Sound := by
  intro candidate present world compatible
  simp only [ofTuple, FiniteSet.mem_singleton] at present
  subst candidate
  exact holds world compatible

/-- Combining sound traces preserves soundness. -/
public theorem sound_union {left right : Trace context model}
    (leftSound : left.Sound) (rightSound : right.Sound) : (left.union right).Sound := by
  intro traced present world compatible
  rcases present with fromLeft | fromRight
  · exact leftSound traced fromLeft world compatible
  · exact rightSound traced fromRight world compatible

/-- A finite union of sound traces is sound. -/
public theorem sound_unions : ∀ {traces : List (Trace context model)},
    (∀ trace, trace ∈ traces → trace.Sound) → (unions traces).Sound
  | [], _ => by
      intro tuple present
      exact False.elim present
  | first :: rest, sound =>
      sound_union (sound first (by simp))
        (sound_unions fun trace present => sound trace (by simp [present]))

end Trace

namespace Instance

variable {World : Type u} {Ty : Type v} {context : Iykyk.Metatheory.Context World}
  {signature : Signature Ty} {model : Model World signature}

/-- Record one origin on every tuple of an instance. -/
@[expose] public def tag (origin : Origin) (data : Instance context model) :
    Trace context model where
  atoms := data.atoms
  tuples := data.tuples
  origins := fun tuple source => tuple ∈ data.tuples ∧ source = origin
  tuplesHaveOrigins := by
    intro tuple
    constructor
    · intro present
      exact ⟨origin, present, rfl⟩
    · rintro ⟨source, present, _⟩
      exact present
  tuplesUseAtoms := data.tuplesUseAtoms

/-- Tagging preserves soundness, since an origin does not change what a tuple means. -/
public theorem sound_tag (origin : Origin) {data : Instance context model} (sound : data.Sound) :
    (data.tag origin).Sound := by
  intro traced present world compatible
  exact sound traced present world compatible

/-- Erasing the origins just recorded gives the instance back. -/
public theorem erase_tag (origin : Origin) (data : Instance context model) :
    (data.tag origin).erase = data := by
  cases data
  rfl

end Instance

namespace Semantics

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World}

/-- The structural trace of an exposed representation: the walk from the selected term's own
atom over the exposed value, with every tuple tagged by how the value was exposed. -/
@[expose] public def structuralTrace (sem : Semantics World L base context) (exposure : Exposure)
    {sort : Ty} (root : Atom context sem.model sort) (value : Term L sort) :
    Trace context sem.model :=
  (sem.walkFrom value root).tag (.structural exposure)

/-- Erasing the exposure tag gives the untagged walk. -/
public theorem erase_structuralTrace (sem : Semantics World L base context) (exposure : Exposure)
    {sort : Ty} (root : Atom context sem.model sort) (value : Term L sort) :
    (sem.structuralTrace exposure root value).erase = sem.walkFrom value root :=
  Instance.erase_tag _ _

/-- The structural trace is sound whenever the root denotes the exposed value. -/
public theorem structuralTrace_sound (sem : Semantics World L base context)
    (exposure : Exposure) {sort : Ty} (root : Atom context sem.model sort) (value : Term L sort)
    (denotes : ∀ world (compatible : context world),
      root world compatible = sem.denote value world compatible) :
    (sem.structuralTrace exposure root value).Sound :=
  Instance.sound_tag _ (sem.walkFrom_sound value root denotes)

/-- If the root denotes the exposed value, its structural trace is, after erasing the exposure
tag, ordinary relationalization of that value. The exposure is recorded but does not influence
which atoms and tuples appear. -/
public theorem erase_structuralTrace_of_denotes (sem : Semantics World L base context)
    (exposure : Exposure) {sort : Ty} {root : Atom context sem.model sort} {value : Term L sort}
    (denotes : ∀ world (compatible : context world),
      root world compatible = sem.denote value world compatible) :
    (sem.structuralTrace exposure root value).erase = sem.relationalize value := by
  have rootEq : root = sem.denote value := funext fun world => funext fun compatible =>
    denotes world compatible
  rw [erase_structuralTrace, relationalize, rootEq]

end Semantics

end SpytialLean.Semantics

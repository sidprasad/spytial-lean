module

public import SpytialLeanInspectionSemantics.Structural

public section

/-!
# Traces: instances that remember where each tuple came from

A trace is a relational instance whose tuples each carry an origin. An origin does not change
what a tuple means, so a trace is sound exactly when the instance obtained by erasing its origins
is sound. The structural walk of an exposed representation is tagged with whether the exposure
came from evaluation or from a checked proof.
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

/-- A tuple together with the origin that justifies it. -/
public structure TracedTuple {Ty : Type u} (signature : Signature Ty) (Entry : Ty → Type v) where
  origin : Origin
  tuple : Tuple signature Entry

/-- A finite positive relational instance whose tuples remember their origin. -/
public structure Trace {World : Type u} {Ty : Type v} (context : Iykyk.Metatheory.Context World)
    {signature : Signature Ty} (model : Model World signature) where
  atoms : List (TypedAtom (Atom context model))
  tuples : List (TracedTuple signature (Atom context model))
  tuplesUseAtoms : ∀ traced, traced ∈ tuples → ∀ atom, atom ∈ traced.tuple.atoms → atom ∈ atoms

namespace Trace

variable {World : Type u} {Ty : Type v} {context : Iykyk.Metatheory.Context World}
  {signature : Signature Ty} {model : Model World signature}

/-- A trace containing one atom and no relational claims. -/
@[expose] public def ofAtom {sort : Ty} (atom : Atom context model sort) : Trace context model where
  atoms := [⟨sort, atom⟩]
  tuples := []
  tuplesUseAtoms := by simp

/-- A trace containing one tuple with the given origin and exactly the atoms it uses. -/
@[expose] public def ofTuple (origin : Origin) (tuple : Tuple signature (Atom context model)) :
    Trace context model where
  atoms := tuple.atoms
  tuples := [⟨origin, tuple⟩]
  tuplesUseAtoms := by
    intro candidate present atom atomPresent
    simp only [List.mem_singleton] at present
    subst candidate
    exact atomPresent

/-- Combine independently obtained traces, keeping every origin. -/
@[expose] public def union (left right : Trace context model) : Trace context model where
  atoms := left.atoms ++ right.atoms
  tuples := left.tuples ++ right.tuples
  tuplesUseAtoms := by
    intro traced present atom atomPresent
    rcases List.mem_append.mp present with fromLeft | fromRight
    · exact List.mem_append_left _ (left.tuplesUseAtoms traced fromLeft atom atomPresent)
    · exact List.mem_append_right _ (right.tuplesUseAtoms traced fromRight atom atomPresent)

/-- Forget every origin. This is the instance consumed by presentation. -/
@[expose] public def erase (trace : Trace context model) : Instance context model where
  atoms := trace.atoms
  tuples := trace.tuples.map TracedTuple.tuple
  tuplesUseAtoms := by
    intro tuple present atom atomPresent
    obtain ⟨traced, tracedPresent, rfl⟩ := List.mem_map.mp present
    exact trace.tuplesUseAtoms traced tracedPresent atom atomPresent

/-- Every tuple of a trace is true in every world allowed by the context. -/
@[expose] public def Sound (trace : Trace context model) : Prop :=
  ∀ traced, traced ∈ trace.tuples → ∀ world (compatible : context world),
    traced.tuple.Holds world compatible

public theorem erase_ofAtom {sort : Ty} (atom : Atom context model sort) :
    (ofAtom atom).erase = Instance.ofAtom atom := rfl

public theorem erase_ofTuple (origin : Origin) (tuple : Tuple signature (Atom context model)) :
    (ofTuple origin tuple).erase = Instance.ofTuple tuple := rfl

public theorem erase_union (left right : Trace context model) :
    (left.union right).erase = left.erase.union right.erase := by
  simp [erase, union, Instance.union]

/-- A trace is sound exactly when its erasure is sound. -/
public theorem sound_iff_erase (trace : Trace context model) :
    trace.Sound ↔ trace.erase.Sound := by
  constructor
  · intro sound tuple present world compatible
    obtain ⟨traced, tracedPresent, rfl⟩ := List.mem_map.mp present
    exact sound traced tracedPresent world compatible
  · intro sound traced present world compatible
    exact sound traced.tuple (List.mem_map.mpr ⟨traced, present, rfl⟩) world compatible

/-- An atom alone makes no relational claim. -/
public theorem sound_ofAtom {sort : Ty} (atom : Atom context model sort) : (ofAtom atom).Sound := by
  simp [Sound, ofAtom]

/-- A singleton trace is sound exactly when its tuple holds; the origin is irrelevant. -/
public theorem sound_ofTuple (origin : Origin) (tuple : Tuple signature (Atom context model))
    (holds : ∀ world (compatible : context world), tuple.Holds world compatible) :
    (ofTuple origin tuple).Sound := by
  intro candidate present world compatible
  simp only [ofTuple, List.mem_singleton] at present
  subst candidate
  exact holds world compatible

/-- Combining sound traces preserves soundness. -/
public theorem sound_union {left right : Trace context model}
    (leftSound : left.Sound) (rightSound : right.Sound) : (left.union right).Sound := by
  intro traced present world compatible
  rcases List.mem_append.mp present with fromLeft | fromRight
  · exact leftSound traced fromLeft world compatible
  · exact rightSound traced fromRight world compatible

end Trace

namespace Instance

variable {World : Type u} {Ty : Type v} {context : Iykyk.Metatheory.Context World}
  {signature : Signature Ty} {model : Model World signature}

/-- Record one origin on every tuple of an instance. -/
@[expose] public def tag (origin : Origin) (data : Instance context model) : Trace context model where
  atoms := data.atoms
  tuples := data.tuples.map fun tuple => ⟨origin, tuple⟩
  tuplesUseAtoms := by
    intro traced present atom atomPresent
    obtain ⟨source, sourcePresent, rfl⟩ := List.mem_map.mp present
    exact data.tuplesUseAtoms source sourcePresent atom atomPresent

/-- Tagging preserves soundness, since an origin does not change what a tuple means. -/
public theorem sound_tag (origin : Origin) {data : Instance context model} (sound : data.Sound) :
    (data.tag origin).Sound := by
  intro traced present world compatible
  obtain ⟨source, sourcePresent, rfl⟩ := List.mem_map.mp present
  exact sound source sourcePresent world compatible

/-- Erasing the origins just recorded gives the instance back. -/
public theorem erase_tag (origin : Origin) (data : Instance context model) :
    (data.tag origin).erase = data := by
  cases data
  simp [Trace.erase, tag, Function.comp_def]

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

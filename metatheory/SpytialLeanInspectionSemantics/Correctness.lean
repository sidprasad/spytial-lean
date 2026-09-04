module

public import SpytialLeanInspectionSemantics.Inspection

public section

/-!
# Correctness of relational inspection

This file proves the properties needed by the inspection semantics:

* every reported tuple is true in every world compatible with the Lean context, using the
  definition of the structural walk rather than an assumed soundness premise;
* one existential proof gives one atom shared by all facts about its witness;
* the evaluation-origin structural trace is ordinary relationalization of the exposed value; and
* a value exposed by proof has the same structural trace as the value exposed by evaluation,
  up to the recorded exposure.
-/

namespace SpytialLean.Semantics

universe u v w x

namespace Exposes

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {program : Program L} {KnowledgeRoot : Type x}
  {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
  {expression value : Term L sort} {exposure : Exposure}

/-- Every exposure, by evaluation or by proof, exposes a value equal to the selected expression. -/
public theorem equalInContext (knowledgeSound : knowledge.Sound context)
    (implements : sem.Implements program)
    (exposes : Exposes sem program knowledge expression value exposure) :
    EqualInContext (sem.denote expression) (sem.denote value) := by
  cases exposes with
  | evaluation evaluates => exact Eval.sound implements evaluates
  | proof known =>
      intro world compatible
      exact knowledgeSound known world compatible compatible

/-- The structural trace of any exposure is sound. -/
public theorem structuralTrace_sound (knowledgeSound : knowledge.Sound context)
    (implements : sem.Implements program)
    (exposes : Exposes sem program knowledge expression value exposure) :
    (sem.structuralTrace exposure (sem.denote expression) value).Sound :=
  sem.structuralTrace_sound exposure _ value (exposes.equalInContext knowledgeSound implements)

/-- Whatever the exposure, its structural trace erases to ordinary relationalization of the
exposed value. -/
public theorem erase_structuralTrace (knowledgeSound : knowledge.Sound context)
    (implements : sem.Implements program)
    (exposes : Exposes sem program knowledge expression value exposure) :
    (sem.structuralTrace exposure (sem.denote expression) value).erase =
      sem.relationalize value :=
  sem.erase_structuralTrace_of_denotes exposure (exposes.equalInContext knowledgeSound implements)

end Exposes

/-- Pointwise equality of contextual atoms is equality of the semantic terms themselves. -/
public theorem atom_eq_of_equalInContext {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty} {left right : Atom context model sort}
    (equal : EqualInContext left right) : left = right := by
  funext world compatible
  exact equal world compatible

/-- Every trace derived by inspection contains only justified tuples. -/
public theorem Inspection.sound {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    {sem : Semantics World L base context} {program : Program L} {KnowledgeRoot : Type x}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
    {expression : Term L sort} {result : Trace context sem.model}
    (implements : sem.Implements program) (knowledgeSound : knowledge.Sound context)
    (inspection : Inspection sem program knowledge expression result) : result.Sound := by
  induction inspection with
  | opaqueTerm => exact Trace.sound_ofAtom _
  | exposed exposes => exact exposes.structuralTrace_sound knowledgeSound implements
  | proved known =>
      apply Trace.sound_ofTuple
      intro world compatible
      exact knowledgeSound known world compatible compatible
  | combine _ _ leftSound rightSound => exact Trace.sound_union leftSound rightSound

/--
One existential proof produces one contextual atom. Both projected facts use that same atom, so a
consumer cannot accidentally draw two unrelated witnesses.

This is a standalone lemma about checked knowledge. No `Inspection` rule introduces a witness
atom, so the inspection judgment does not yet expose existential witnesses; the lemma records the
property such a rule would have to preserve.
-/
public theorem checked_existential_has_shared_atom
    {World : Type u} {Ty : Type v} {KnowledgeRoot : Type w}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}
    {left right : World → model.Carrier sort → Prop}
    (knowledgeSound : knowledge.Sound context)
    (known : (fun world => ∃ value, left world value ∧ right world value) ∈ knowledge.facts) :
    ∃ witness : Atom context model sort,
      (∀ world (compatible : context world), left world (witness world compatible)) ∧
      (∀ world (compatible : context world), right world (witness world compatible)) := by
  have proof : Iykyk.Metatheory.Entails context
      (fun world => ∃ value, left world value ∧ right world value) :=
    knowledgeSound known
  let witness := fun world compatible => Classical.choose (proof world compatible)
  refine ⟨witness, ?_, ?_⟩
  · intro world compatible
    exact (Classical.choose_spec (proof world compatible)).1
  · intro world compatible
    exact (Classical.choose_spec (proof world compatible)).2

section Agreement

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {program : Program L} {KnowledgeRoot : Type x}
  {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
  {expression value : Term L sort}

/-- If `e -->op v`, the evaluation-origin structural trace of `e` is, after erasing the exposure
tag, ordinary relationalization of `v`. -/
public theorem evaluation_trace_is_relationalization (implements : sem.Implements program)
    (evaluates : Eval program expression value) :
    (sem.structuralTrace .evaluation (sem.denote expression) value).erase =
      sem.relationalize value :=
  sem.erase_structuralTrace_of_denotes .evaluation (Eval.sound implements evaluates)

/-- If checked knowledge contains `e = v`, the proof-origin structural trace of `e` is, after
erasing the exposure tag, ordinary relationalization of `v`. -/
public theorem proof_trace_is_relationalization (knowledgeSound : knowledge.Sound context)
    (known : equalityFact (sem.denote expression) (sem.denote value) ∈ knowledge.facts) :
    (sem.structuralTrace .proof (sem.denote expression) value).erase =
      sem.relationalize value :=
  sem.erase_structuralTrace_of_denotes .proof fun world compatible =>
    knowledgeSound known world compatible compatible

/--
If evaluation and a checked equality expose the same `v`, the proof-origin structural trace and
the evaluation-origin structural trace agree exactly once the exposure tag is erased. The walk
reads only the root atom and the exposed representation, so the tag is the only difference.
-/
public theorem proof_reveals_same_structure_as_computation
    (knowledgeSound : knowledge.Sound context) (implements : sem.Implements program)
    (evaluates : Eval program expression value)
    (known : equalityFact (sem.denote expression) (sem.denote value) ∈ knowledge.facts) :
    (sem.structuralTrace .proof (sem.denote expression) value).erase =
      (sem.structuralTrace .evaluation (sem.denote expression) value).erase := by
  rw [proof_trace_is_relationalization knowledgeSound known,
    evaluation_trace_is_relationalization implements evaluates]

/--
The main result packages the central guarantees: an inspection built on the proof-exposed
structure is derivable and sound, it retains ordinary relationalization of the evaluated value,
and its structural trace agrees with the evaluation-origin trace up to the recorded exposure.
-/
public theorem proof_aware_inspection_agrees_with_computation
    {additional : Trace context sem.model}
    (knowledgeSound : knowledge.Sound context) (implements : sem.Implements program)
    (evaluates : Eval program expression value)
    (known : equalityFact (sem.denote expression) (sem.denote value) ∈ knowledge.facts)
    (additionalInspection : Inspection sem program knowledge expression additional) :
    let result := (sem.structuralTrace .proof (sem.denote expression) value).union additional
    Inspection sem program knowledge expression result ∧
      result.Sound ∧
      Instance.ContainedIn (sem.relationalize value) result.erase ∧
      (sem.structuralTrace .proof (sem.denote expression) value).erase =
        (sem.structuralTrace .evaluation (sem.denote expression) value).erase := by
  have structuralInspection :
      Inspection sem program knowledge expression
        (sem.structuralTrace .proof (sem.denote expression) value) :=
    .exposed (.proof known)
  have combined := Inspection.combine structuralInspection additionalInspection
  refine ⟨combined, combined.sound implements knowledgeSound, ?_,
    proof_reveals_same_structure_as_computation knowledgeSound implements evaluates known⟩
  rw [Trace.erase_union, proof_trace_is_relationalization knowledgeSound known]
  exact Instance.containedIn_union_left _ _

end Agreement

end SpytialLean.Semantics

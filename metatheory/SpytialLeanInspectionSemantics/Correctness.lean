module

public import SpytialLeanInspectionSemantics.Inspection

public section

/-!
# Correctness of relational inspection

This file proves the properties needed by the inspection semantics:

* every reported tuple is true in every world compatible with the Lean context, using the
  definition of the structural walk rather than an assumed soundness premise;
* canonical inspection contains every contribution in a complete finite plan and conservatively
  extends ordinary relationalization whenever evaluation succeeds;
* one existential proof gives one atom shared by all facts about its witness;
* the evaluation-origin structural trace is ordinary relationalization of the exposed value; and
* an independently supplied proof representation normalized to the same residual has the same
  structural trace as direct evaluation, up to the recorded exposure.
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
  | proof known normalizes =>
      intro world compatible
      calc
        sem.denote expression world compatible = sem.denote _ world compatible :=
          knowledgeSound known world compatible compatible
        _ = sem.denote value world compatible := Eval.sound implements normalizes world compatible

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

namespace ExposureContribution

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {program : Program L} {KnowledgeRoot : Type x}
  {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
  {expression : Term L sort}

/-- Every inventoried exposure contribution is sound. -/
public theorem trace_sound (contribution : ExposureContribution sem program knowledge expression)
    (knowledgeSound : knowledge.Sound context) (implements : sem.Implements program) :
    contribution.trace.Sound :=
  contribution.evidence.structuralTrace_sound knowledgeSound implements

end ExposureContribution

namespace KnowledgeContribution

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {KnowledgeRoot : Type x} {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}

/-- Every inventoried retained tuple is sound by the checked knowledge contract. -/
public theorem trace_sound (contribution : KnowledgeContribution sem knowledge)
    (knowledgeSound : knowledge.Sound context) : contribution.trace.Sound := by
  apply Trace.sound_ofTuple
  intro world compatible
  exact knowledgeSound contribution.known world compatible compatible

end KnowledgeContribution

/-- The canonical inspection result retains any exposure contribution listed in its plan. -/
public theorem inspect_contains_exposure
    {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
    {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
    {program : Program L} {KnowledgeRoot : Type x}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
    {expression : Term L sort} (plan : InspectionPlan sem program knowledge expression)
    (contribution : ExposureContribution sem program knowledge expression)
    (present : contribution ∈ plan.exposures) :
    contribution.trace.ContainedIn (inspect sem program knowledge expression plan) := by
  have listed : contribution.trace ∈ plan.exposures.map ExposureContribution.trace :=
    List.mem_map.mpr ⟨contribution, present, rfl⟩
  exact (Trace.containedIn_unions_of_mem listed).trans
    ((Trace.containedIn_union_left _ _).trans (Trace.containedIn_union_right _ _))

/-- The canonical inspection result retains any checked tuple listed in its plan. -/
public theorem inspect_contains_knowledge
    {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
    {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
    {program : Program L} {KnowledgeRoot : Type x}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
    {expression : Term L sort} (plan : InspectionPlan sem program knowledge expression)
    (contribution : KnowledgeContribution sem knowledge)
    (present : contribution ∈ plan.tuples) :
    contribution.trace.ContainedIn (inspect sem program knowledge expression plan) := by
  have listed : contribution.trace ∈ plan.tuples.map KnowledgeContribution.trace :=
    List.mem_map.mpr ⟨contribution, present, rfl⟩
  exact (Trace.containedIn_unions_of_mem listed).trans
    ((Trace.containedIn_union_right _ _).trans (Trace.containedIn_union_right _ _))

/-- Canonical inspection contains only justified tuples. -/
public theorem inspect_sound
    {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
    {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
    {program : Program L} {KnowledgeRoot : Type x}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
    {expression : Term L sort} (plan : InspectionPlan sem program knowledge expression)
    (knowledgeSound : knowledge.Sound context) (implements : sem.Implements program) :
    (inspect sem program knowledge expression plan).Sound := by
  apply Trace.sound_union (Trace.sound_ofAtom _)
  apply Trace.sound_union
  · apply Trace.sound_unions
    intro trace present
    obtain ⟨contribution, _, rfl⟩ := List.mem_map.mp present
    exact contribution.trace_sound knowledgeSound implements
  · apply Trace.sound_unions
    intro trace present
    obtain ⟨contribution, _, rfl⟩ := List.mem_map.mp present
    exact contribution.trace_sound knowledgeSound

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
  {expression representation value : Term L sort}

/-- If `e -->op v`, the evaluation-origin structural trace of `e` is, after erasing the exposure
tag, ordinary relationalization of `v`. -/
public theorem evaluation_trace_is_relationalization (implements : sem.Implements program)
    (evaluates : Eval program expression value) :
    (sem.structuralTrace .evaluation (sem.denote expression) value).erase =
      sem.relationalize value :=
  sem.erase_structuralTrace_of_denotes .evaluation (Eval.sound implements evaluates)

/-- If checked knowledge contains `e = representation` and that representation evaluates to `v`,
the proof-origin structural trace is ordinary relationalization of the normalized `v`. -/
public theorem proof_trace_is_relationalization (knowledgeSound : knowledge.Sound context)
    (implements : sem.Implements program)
    (known : equalityFact (sem.denote expression) (sem.denote representation) ∈ knowledge.facts)
    (normalizes : Eval program representation value) :
    (sem.structuralTrace .proof (sem.denote expression) value).erase =
      sem.relationalize value :=
  (Exposes.proof known normalizes).erase_structuralTrace knowledgeSound implements

/--
Evaluation may start at `expression` while proof exposure starts at an independently supplied
`representation`. When both evaluate to the same residual `value`, their structural traces agree
after erasing provenance. This compares the results after the shared normalization step rather
than assuming both sources initially supplied the same representation.
-/
public theorem normalized_proof_trace_agrees_with_evaluation
    (knowledgeSound : knowledge.Sound context) (implements : sem.Implements program)
    (evaluates : Eval program expression value)
    (known : equalityFact (sem.denote expression) (sem.denote representation) ∈ knowledge.facts)
    (normalizes : Eval program representation value) :
    (sem.structuralTrace .proof (sem.denote expression) value).erase =
      (sem.structuralTrace .evaluation (sem.denote expression) value).erase := by
  rw [proof_trace_is_relationalization knowledgeSound implements known normalizes,
    evaluation_trace_is_relationalization implements evaluates]

/-- Completeness of the plan makes canonical inspection retain every applicable exposure. -/
public theorem inspect_contains_every_exposure
    (plan : InspectionPlan sem program knowledge expression) (complete : plan.Complete)
    {source : Exposure} (exposes : Exposes sem program knowledge expression value source) :
    (sem.structuralTrace source (sem.denote expression) value).ContainedIn
      (inspect sem program knowledge expression plan) := by
  obtain ⟨contribution, present, valueEq, sourceEq⟩ := complete.exposures exposes
  cases valueEq
  cases sourceEq
  exact inspect_contains_exposure plan contribution present

/-- Completeness of the plan likewise retains every checked relational tuple. -/
public theorem inspect_contains_every_knowledge_tuple
    (plan : InspectionPlan sem program knowledge expression) (complete : plan.Complete)
    (tuple : Tuple (base.withFields L) (Atom context sem.model))
    (known : tuple.fact ∈ knowledge.facts) :
    (Trace.ofTuple .knowledge tuple).ContainedIn
      (inspect sem program knowledge expression plan) := by
  obtain ⟨contribution, present, tupleEq⟩ := complete.tuples tuple known
  cases tupleEq
  exact inspect_contains_knowledge plan contribution present

/-- The canonical result, unlike one arbitrary derivation of the permissive `Inspection` judgment,
is sound and conservatively extends ordinary relationalization whenever evaluation succeeds. -/
public theorem canonical_inspection_sound_and_contains_evaluation
    (plan : InspectionPlan sem program knowledge expression) (complete : plan.Complete)
    (knowledgeSound : knowledge.Sound context) (implements : sem.Implements program)
    (evaluates : Eval program expression value) :
    let result := inspect sem program knowledge expression plan
    result.Sound ∧ Instance.ContainedIn (sem.relationalize value) result.erase := by
  refine ⟨inspect_sound plan knowledgeSound implements, ?_⟩
  have contained := Trace.erase_containedIn
    (inspect_contains_every_exposure plan complete (Exposes.evaluation evaluates))
  rw [evaluation_trace_is_relationalization implements evaluates] at contained
  exact contained

end Agreement

end SpytialLean.Semantics

module

public import Inspection

public section

/-!
# Correctness of relational inspection

This file proves the three properties needed by the inspection semantics:

* every reported tuple is true in every world compatible with the Lean context;
* one existential proof gives one atom shared by all facts about its witness; and
* a value exposed by proof has the same structural relationalization as the value exposed by
  computation.
-/

namespace SpytialLean.Semantics

universe u v w

namespace Resolution

/-- Every valid resolution exposes a value equal to the selected expression. -/
public theorem equalInContext {World : Type u} {Ty : Type v} {KnowledgeRoot : Type w}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {rootSort : Ty}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}
    {expression value : Atom context model rootSort}
    (knowledgeSound : knowledge.Sound context)
    (resolution : Resolution knowledge expression value) : EqualInContext expression value := by
  cases resolution with
  | computation computes => exact computes
  | proof known =>
      intro world compatible
      exact knowledgeSound known world compatible compatible

end Resolution

/-- Pointwise equality of contextual atoms is equality of the semantic terms themselves. -/
public theorem atom_eq_of_equalInContext {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty} {left right : Atom context model sort}
    (equal : EqualInContext left right) : left = right := by
  funext world compatible
  exact equal world compatible

/-- Every instance derived by inspection contains only justified tuples. -/
public theorem Inspection.sound {World : Type u} {Ty : Type v} {KnowledgeRoot : Type w}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {rootSort : Ty}
    {relationalize : StructuralRelationalizer (context := context) model rootSort}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}
    {expression : Atom context model rootSort} {result : Instance context model}
    (structuralSound : StructuralSound relationalize)
    (knowledgeSound : knowledge.Sound context)
    (inspection : Inspection relationalize knowledge expression result) : result.Sound := by
  induction inspection with
  | opaqueTerm => exact Instance.sound_ofAtom expression
  | resolved resolution => exact structuralSound _
  | proved known =>
      apply Instance.sound_ofTuple
      intro world compatible
      exact knowledgeSound known world compatible compatible
  | combine _ _ leftSound rightSound => exact Instance.sound_union leftSound rightSound

/--
One existential proof produces one contextual atom. Both projected facts use that same atom, so a
consumer cannot accidentally draw two unrelated witnesses.
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

/--
If computation and proof expose the selected expression, ordinary relationalization sees the same
structure from either source.
-/
public theorem proof_reveals_same_structure_as_computation
    {World : Type u} {Ty : Type v} {KnowledgeRoot : Type w}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {rootSort : Ty}
    (relationalize : StructuralRelationalizer (context := context) model rootSort)
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}
    {expression computedValue provedValue : Atom context model rootSort}
    (knowledgeSound : knowledge.Sound context)
    (computed : ComputesTo expression computedValue)
    (proved : equalityFact expression provedValue ∈ knowledge.facts) :
    relationalize computedValue = relationalize provedValue := by
  have provedEqual : EqualInContext expression provedValue :=
    Resolution.equalInContext knowledgeSound (.proof proved)
  have valuesEqual : computedValue = provedValue :=
    atom_eq_of_equalInContext fun world compatible =>
      (computed world compatible).symm.trans (provedEqual world compatible)
  exact congrArg relationalize valuesEqual

/--
The main result packages the two central guarantees: an inspection result is sound, and the
structural view is independent of whether computation or proof exposed the value.
-/
public theorem proof_aware_inspection_agrees_with_computation
    {World : Type u} {Ty : Type v} {KnowledgeRoot : Type w}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {rootSort : Ty}
    {relationalize : StructuralRelationalizer (context := context) model rootSort}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}
    {expression computedValue provedValue : Atom context model rootSort}
    {additional : Instance context model}
    (structuralSound : StructuralSound relationalize)
    (knowledgeSound : knowledge.Sound context)
    (computed : ComputesTo expression computedValue)
    (proved : equalityFact expression provedValue ∈ knowledge.facts)
    (additionalInspection : Inspection relationalize knowledge expression additional) :
    let result := (relationalize provedValue).union additional
    Inspection relationalize knowledge expression result ∧
      result.Sound ∧
      Instance.ContainedIn (relationalize computedValue) result ∧
      relationalize computedValue = relationalize provedValue := by
  have agreement :=
    proof_reveals_same_structure_as_computation relationalize knowledgeSound computed proved
  have structuralInspection :
      Inspection relationalize knowledge expression (relationalize provedValue) :=
    .resolved (.proof proved)
  have combined := Inspection.combine structuralInspection additionalInspection
  refine ⟨combined, combined.sound structuralSound knowledgeSound, ?_, agreement⟩
  rw [agreement]
  exact Instance.containedIn_union_left _ _

end SpytialLean.Semantics

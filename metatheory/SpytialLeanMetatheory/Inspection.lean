module

public import SpytialLeanMetatheory.Knowledge

public section

/-!
# Relational inspection by computation or proof

The central operation first obtains a representation of the selected term.
Computation may obtain it by reduction; a proof may obtain it from an equality
in the context. The ordinary structural relationalizer then receives that
representation. Proof-derived tuples are a positive extension of its result.

The ordinary structural relationalizer is a parameter because Spytial already
has that producer. This development proves the new composition theorem rather
than attempting to verify Lean's evaluator or the whole production walker.
-/

namespace SpytialLean.Metatheory

universe u v w x y

/-- A value whose interpretation may depend on the possible world and on
    evidence that the world satisfies the current context. -/
public abbrev ContextualValue {World : Type u}
    (context : Iykyk.Metatheory.Context World) (Value : Type v) :=
  ∀ world, context world → Value

/-- Two contextual values agree in every world admitted by the context. -/
@[expose] public def EqualInContext {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    (left right : ContextualValue context Value) : Prop :=
  ∀ world (compatible : context world), left world compatible = right world compatible

/-- Contextual equality expressed as an IYKYK possible-world fact. -/
@[expose] public def equalityFact {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    (left right : ContextualValue context Value) : Iykyk.Metatheory.Fact World :=
  fun world => ∀ compatible : context world,
    left world compatible = right world compatible

/-- Pointwise contextual equality gives equality of contextual values. -/
public theorem contextualValue_eq {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    {left right : ContextualValue context Value}
    (equal : EqualInContext left right) : left = right := by
  funext world compatible
  exact equal world compatible

/-- A representation obtained by computation. `evaluates` is the semantic
    result of reduction, not a model of Lean's evaluator. -/
public structure ComputationResult {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    (expression : ContextualValue context Value) where
  value : ContextualValue context Value
  evaluates : EqualInContext expression value

/-- A representation obtained from a contextual equality proof. -/
public structure ProofResult {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    (expression : ContextualValue context Value) where
  value : ContextualValue context Value
  proves : Iykyk.Metatheory.Entails context (equalityFact expression value)

namespace ProofResult

/-- Build a proof resolution directly from an equality retained by sound IYKYK
    knowledge. This is the semantic counterpart of selecting a checked equality
    from `Afaik`. -/
public def ofKnowledge {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    {expression value : ContextualValue context Value}
    (knowledge : Iykyk.Metatheory.Knowledge World Value)
    (knowledgeSound : knowledge.Sound context)
    (present : equalityFact expression value ∈ knowledge.facts) :
    ProofResult expression where
  value
  proves := knowledgeSound present

/-- A proved equality gives the same pointwise agreement as evaluation. -/
public theorem equalInContext {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    {expression : ContextualValue context Value}
    (result : ProofResult expression) : EqualInContext expression result.value := by
  intro world compatible
  exact result.proves world compatible compatible

end ProofResult

/-- The two supported ways to obtain the representation that inspection walks. -/
public inductive Resolution {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    (expression : ContextualValue context Value) where
  | computation (result : ComputationResult expression)
  | proof (result : ProofResult expression)

namespace Resolution

/-- The representation selected by a resolution. -/
@[expose] public def value {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    {expression : ContextualValue context Value} :
    Resolution expression → ContextualValue context Value
  | .computation result => result.value
  | .proof result => result.value

/-- Either knowledge source selects a value equal to the inspected expression. -/
public theorem correct {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    {expression : ContextualValue context Value}
    (resolution : Resolution expression) :
    EqualInContext expression resolution.value := by
  cases resolution with
  | computation result => exact result.evaluates
  | proof result => exact result.equalInContext

/-- Any two valid resolutions of one expression select the same semantic value. -/
public theorem values_eq {World : Type u} {Value : Type v}
    {context : Iykyk.Metatheory.Context World}
    {expression : ContextualValue context Value}
    (left right : Resolution expression) : left.value = right.value := by
  apply contextualValue_eq
  intro world compatible
  exact (left.correct world compatible).symm.trans (right.correct world compatible)

end Resolution

/-- The existing ordinary relationalizer, stated at the semantic boundary used
    here. Its structural soundness is the prior component on which proof-aware
    inspection builds. -/
public structure StructuralRelationalizer {World : Type u}
    {SemanticType : Type v}
    (context : Iykyk.Metatheory.Context World)
    (Value : Type w)
    (signature : RelationalSignature SemanticType)
    {model : RelationalModel World signature}
    (Entry : SemanticType → Type x)
    (interpretation : AtomInterpretation context model Entry) where
  relationalize : ContextualValue context Value → RelationalData signature Entry
  sound : ∀ value, Sound context interpretation (relationalize value)

/-- Proof-aware inspection retains the ordinary structural result and adds
    only tuples decoded from certified contextual knowledge. -/
public structure Inspection {World : Type u} {SemanticType : Type v}
    {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    (relationalizer : StructuralRelationalizer context Value signature Entry interpretation)
    (knowledge : Iykyk.Metatheory.Knowledge World Value)
    (expression : ContextualValue context Value) where
  resolution : Resolution expression
  decoded : DecodedKnowledge interpretation knowledge

namespace Inspection

/-- The structural part of inspection is exactly ordinary relationalization
    of the value obtained from computation or proof. -/
@[expose] public def root {World : Type u} {SemanticType : Type v}
    {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {relationalizer : StructuralRelationalizer context Value signature Entry interpretation}
    {knowledge : Iykyk.Metatheory.Knowledge World Value}
    {expression : ContextualValue context Value}
    (inspection : Inspection relationalizer knowledge expression) :
    RelationalData signature Entry :=
  relationalizer.relationalize inspection.resolution.value

/-- The full instance sent to Spytial: structure followed by proof refinement. -/
@[expose] public def data {World : Type u} {SemanticType : Type v}
    {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {relationalizer : StructuralRelationalizer context Value signature Entry interpretation}
    {knowledge : Iykyk.Metatheory.Knowledge World Value}
    {expression : ContextualValue context Value}
    (inspection : Inspection relationalizer knowledge expression) :
    RelationalData signature Entry :=
  inspection.root.union inspection.decoded.data

/-- Every inspected tuple is true in every context-compatible world. -/
public theorem sound {World : Type u} {SemanticType : Type v}
    {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {relationalizer : StructuralRelationalizer context Value signature Entry interpretation}
    {knowledge : Iykyk.Metatheory.Knowledge World Value}
    {expression : ContextualValue context Value}
    (inspection : Inspection relationalizer knowledge expression)
    (knowledgeSound : knowledge.Sound context) :
    Sound context interpretation inspection.data :=
  sound_union (relationalizer.sound inspection.resolution.value)
    (inspection.decoded.sound knowledgeSound)

/-- Proof-aware inspection is a positive refinement of ordinary
    relationalization; it never removes structural atoms or tuples. -/
public theorem retains_ordinary_relationalization {World : Type u}
    {SemanticType : Type v} {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {relationalizer : StructuralRelationalizer context Value signature Entry interpretation}
    {knowledge : Iykyk.Metatheory.Knowledge World Value}
    {expression : ContextualValue context Value}
    (inspection : Inspection relationalizer knowledge expression) :
    RelationalData.ContainedIn inspection.root inspection.data :=
  RelationalData.containedIn_union_left _ _

/-- The root of proof-aware inspection agrees with ordinary relationalization
    for any other valid way of resolving the same expression. -/
public theorem root_agrees_with_ordinary_relationalization {World : Type u}
    {SemanticType : Type v} {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {relationalizer : StructuralRelationalizer context Value signature Entry interpretation}
    {knowledge : Iykyk.Metatheory.Knowledge World Value}
    {expression : ContextualValue context Value}
    (inspection : Inspection relationalizer knowledge expression)
    (ordinary : Resolution expression) :
    inspection.root = relationalizer.relationalize ordinary.value := by
  exact congrArg relationalizer.relationalize
    (inspection.resolution.values_eq ordinary)

/-- **Inspection soundness and agreement.** When computation can resolve the
    selected expression, proof-aware inspection is sound, contains the ordinary
    computed relationalization, and has exactly that relationalization as its
    structural root. -/
public theorem soundly_refines_computed_relationalization
    {World : Type u} {SemanticType : Type v} {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    {relationalizer : StructuralRelationalizer context Value signature Entry interpretation}
    {knowledge : Iykyk.Metatheory.Knowledge World Value}
    {expression : ContextualValue context Value}
    (inspection : Inspection relationalizer knowledge expression)
    (computed : ComputationResult expression)
    (knowledgeSound : knowledge.Sound context) :
    Sound context interpretation inspection.data ∧
      RelationalData.ContainedIn
        (relationalizer.relationalize computed.value) inspection.data ∧
      inspection.root = relationalizer.relationalize computed.value := by
  have agreement : inspection.root = relationalizer.relationalize computed.value :=
    inspection.root_agrees_with_ordinary_relationalization (.computation computed)
  refine ⟨inspection.sound knowledgeSound, ?_, agreement⟩
  rw [← agreement]
  exact inspection.retains_ordinary_relationalization

end Inspection

/-- **Knowledge-source independence.** If computation and proof both resolve
    one expression, ordinary relationalization produces the same structural
    instance from either result. -/
public theorem computation_and_proof_have_same_relational_structure
    {World : Type u} {SemanticType : Type v} {Value : Type w}
    {context : Iykyk.Metatheory.Context World}
    {signature : RelationalSignature SemanticType}
    {model : RelationalModel World signature}
    {Entry : SemanticType → Type x}
    {interpretation : AtomInterpretation context model Entry}
    (relationalizer : StructuralRelationalizer context Value signature Entry interpretation)
    {expression : ContextualValue context Value}
    (computed : ComputationResult expression)
    (proved : ProofResult expression) :
    relationalizer.relationalize computed.value =
      relationalizer.relationalize proved.value := by
  exact congrArg relationalizer.relationalize
    (Resolution.values_eq (.computation computed) (.proof proved))

end SpytialLean.Metatheory

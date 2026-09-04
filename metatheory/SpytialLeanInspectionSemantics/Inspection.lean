module

public import SpytialLeanInspectionSemantics.Trace

public section

/-!
# Inspection by computation and proof

The selected term and every value exposed from it are typed semantic atoms. A constructor-headed
representation of the term is exposed in one of two genuinely different ways:

```text
e -->op v
------------------------------- EXPOSE-EVAL
Gamma ; K |-expose e => v @ eval

(e = v, pi) in K
----------------------------------- EXPOSE-PROOF
Gamma ; K |-expose e => v @ proof pi
```

`Exposes` is the judgment. The first rule uses the operational semantics `Eval`; the second reads
an equality from checked IYKYK knowledge and evaluates the proof-supplied representation before
walking it. Both therefore run the same defined structural walk over an evaluated residual,
rooted at the atom for `e`, and record the exposure in the trace.

The proof `pi` is not modelled: knowledge soundness stands in for it.
-/

namespace SpytialLean.Semantics

universe u v w x

/-- Two typed atoms denote the same value in every world allowed by the context. -/
@[expose] public def EqualInContext {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty}
    (left right : Atom context model sort) : Prop :=
  ∀ world (compatible : context world), left world compatible = right world compatible

/-- Contextual equality represented as an IYKYK fact. -/
@[expose] public def equalityFact {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty}
    (left right : Atom context model sort) : Iykyk.Metatheory.Fact World :=
  fun world => ∀ compatible : context world,
    left world compatible = right world compatible

/-- Exposure of a representation of `expression`, recording how it was obtained. -/
public inductive Exposes {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) (program : Program L) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) {sort : Ty}
    (expression : Term L sort) : Term L sort → Exposure → Prop where
  /-- EXPOSE-EVAL: the expression evaluates to `value`. -/
  | evaluation {value} (evaluates : Eval program expression value) :
      Exposes sem program knowledge expression value .evaluation
  /-- EXPOSE-PROOF: checked knowledge contains `expression = representation`, then the same
  operational semantics used by EXPOSE-EVAL normalizes that representation before walking it. -/
  | proof {representation value}
      (known : equalityFact (sem.denote expression) (sem.denote representation) ∈ knowledge.facts)
      (normalizes : Eval program representation value) :
      Exposes sem program knowledge expression value .proof

/--
The inspection judgment. It contains only the rules needed by the central claim:

* retain an opaque term as an atom;
* walk structure exposed by evaluation or proof, keeping the exposure in the trace;
* report a tuple backed by checked knowledge; and
* combine independently justified observations.

The judgment records how each reported observation is justified. It does not say that an
observation is about `expression`: `proved` accepts any tuple whose fact is in `knowledge`, and
`combine` accepts any two justified traces. Relevance to the selected expression is not
modelled here. Decoding a proved proposition into a tuple is also not modelled: `proved` starts
from a tuple whose fact is already in knowledge.
-/
public inductive Inspection {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) (program : Program L) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) {sort : Ty}
    (expression : Term L sort) : Trace context sem.model → Prop where
  | opaqueTerm :
      Inspection sem program knowledge expression (Trace.ofAtom (sem.denote expression))
  /-- Walk the exposed representation from the expression's own atom. -/
  | exposed {value exposure} (exposes : Exposes sem program knowledge expression value exposure) :
      Inspection sem program knowledge expression
        (sem.structuralTrace exposure (sem.denote expression) value)
  /-- Report a tuple backed by checked knowledge. The tuple need not mention `expression`. -/
  | proved {tuple : Tuple (base.withFields L) (Atom context sem.model)}
      (known : tuple.fact ∈ knowledge.facts) :
      Inspection sem program knowledge expression (Trace.ofTuple .knowledge tuple)
  | combine {left right}
      (leftInspection : Inspection sem program knowledge expression left)
      (rightInspection : Inspection sem program knowledge expression right) :
      Inspection sem program knowledge expression (left.union right)

/-- One finite exposure contribution selected by an inspection producer. The evidence ensures the
entry can only describe an applicable evaluation or retained-proof exposure. -/
public structure ExposureContribution {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) (program : Program L) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) {sort : Ty}
    (expression : Term L sort) where
  value : Term L sort
  source : Exposure
  evidence : Exposes sem program knowledge expression value source

namespace ExposureContribution

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {program : Program L} {KnowledgeRoot : Type x}
  {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
  {expression : Term L sort}

/-- Materialize one exposure contribution as a structural trace. -/
@[expose] public def trace
    (contribution : ExposureContribution sem program knowledge expression) :
    Trace context sem.model :=
  sem.structuralTrace contribution.source (sem.denote expression) contribution.value

end ExposureContribution

/-- One retained checked tuple selected by an inspection producer. -/
public structure KnowledgeContribution {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) where
  tuple : Tuple (base.withFields L) (Atom context sem.model)
  known : tuple.fact ∈ knowledge.facts

namespace KnowledgeContribution

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {KnowledgeRoot : Type x} {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}

/-- Materialize one checked tuple with its knowledge origin. -/
@[expose] public def trace (contribution : KnowledgeContribution sem knowledge) :
    Trace context sem.model :=
  Trace.ofTuple .knowledge contribution.tuple

end KnowledgeContribution

/-- The finite inventory consumed by canonical inspection. It separates discovery from assembly:
every listed contribution carries its evidence, while `Complete` below states that discovery did
not omit any applicable exposure or retained tuple. -/
public structure InspectionPlan {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) (program : Program L) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) {sort : Ty}
    (expression : Term L sort) where
  exposures : List (ExposureContribution sem program knowledge expression)
  tuples : List (KnowledgeContribution sem knowledge)

namespace InspectionPlan

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {program : Program L} {KnowledgeRoot : Type x}
  {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
  {expression : Term L sort}

/-- A plan is closed when it inventories every applicable exposure and every retained tuple. This
is the explicit completeness boundary for a finite extractor. -/
public structure Complete (plan : InspectionPlan sem program knowledge expression) : Prop where
  exposures : ∀ {value source}, Exposes sem program knowledge expression value source →
    ∃ contribution, contribution ∈ plan.exposures ∧
      contribution.value = value ∧ contribution.source = source
  tuples : ∀ (tuple : Tuple (base.withFields L) (Atom context sem.model)),
    tuple.fact ∈ knowledge.facts →
      ∃ contribution, contribution ∈ plan.tuples ∧ contribution.tuple = tuple

end InspectionPlan

/-- Canonical closed-world assembly for one finite inspection inventory. The root, every exposure,
and every retained tuple are combined exactly once at the set level; duplicate discoveries merge
while their origins are preserved. -/
@[expose] public def inspect {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) (program : Program L) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) {sort : Ty}
    (expression : Term L sort) (plan : InspectionPlan sem program knowledge expression) :
    Trace context sem.model :=
  (Trace.ofAtom (sem.denote expression)).union
    ((Trace.unions (plan.exposures.map ExposureContribution.trace)).union
      (Trace.unions (plan.tuples.map KnowledgeContribution.trace)))

end SpytialLean.Semantics

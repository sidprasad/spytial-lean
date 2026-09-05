module

public import SpytialLeanInspectionSemantics.Decoder
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
* retain evaluated points of owned operation graphs;
* decode a supported checked proposition to a tuple; and
* combine independently justified observations.

The judgment records how each reported observation is justified. It does not say that an
observation is about `expression`: `proved` accepts any supported checked proposition in
`knowledge`, and `combine` accepts any two justified traces. Relevance to the selected expression
is the finite producer's responsibility.
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
  /-- Retain a computed point of an owned named operation's graph. -/
  | computed {operation : L.Op} {arguments : Arguments (Term L) (L.params operation)}
      {result : Term L (L.opResult operation)}
      (evaluates : Eval program (.op operation arguments) result) :
      Inspection sem program knowledge expression
        (Trace.ofTuple .computation (sem.graphTuple operation arguments result))
  /-- Report the tuple obtained by the defined decoder from a checked proposition. -/
  | proved {proposition : Proposition L base}
      {tuple : Tuple (base.withFields L) (Atom context sem.model)}
      (known : proposition.fact sem ∈ knowledge.facts) (decoded : sem.Decodes proposition tuple) :
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

/-- One computed function-graph point selected by the inspection producer. -/
public structure ComputationContribution {World : Type w} {Ty : Type u}
    {L : Language.{u, v} Ty} {base : Signature Ty}
    {context : Iykyk.Metatheory.Context World} (sem : Semantics World L base context)
    (program : Program L) where
  operation : L.Op
  arguments : Arguments (Term L) (L.params operation)
  result : Term L (L.opResult operation)
  evaluates : Eval program (.op operation arguments) result

namespace ComputationContribution

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {program : Program L}

/-- Materialize one evaluated operation as a graph tuple. -/
@[expose] public def trace (contribution : ComputationContribution sem program) :
    Trace context sem.model :=
  Trace.ofTuple .computation
    (sem.graphTuple contribution.operation contribution.arguments contribution.result)

end ComputationContribution

/-- One existential witness retained by the IYKYK snapshot boundary. `term` is the shared term
used by every decomposed fact below the existential; `realizes` is the witness-aware certificate
that the production extractor obtains from the checked proof. -/
public structure WitnessContribution {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) where
  sort : Ty
  term : Term L sort
  left : World → sem.Carrier sort → Prop
  rightPredicate : World → sem.Carrier sort → Prop
  known : (fun world => ∃ value, left world value ∧ rightPredicate world value) ∈
    knowledge.facts
  realizes : ∀ world (compatible : context world),
    left world (sem.denote term world compatible) ∧
      rightPredicate world (sem.denote term world compatible)

namespace WitnessContribution

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
  {KnowledgeRoot : Type x} {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}

/-- Materialize the shared existential term as one typed atom. -/
@[expose] public def trace (contribution : WitnessContribution sem knowledge) :
    Trace context sem.model :=
  Trace.ofAtom (sem.denote contribution.term)

end WitnessContribution

/-- One supported checked proposition and its decoder output, selected by an inspection producer. -/
public structure KnowledgeContribution {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) where
  proposition : Proposition L base
  tuple : Tuple (base.withFields L) (Atom context sem.model)
  known : proposition.fact sem ∈ knowledge.facts
  decoded : sem.Decodes proposition tuple

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
  witnesses : List (WitnessContribution sem knowledge) := []
  computations : List (ComputationContribution sem program) := []
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
  tuples : ∀ (proposition : Proposition L base)
    (tuple : Tuple (base.withFields L) (Atom context sem.model)),
    proposition.fact sem ∈ knowledge.facts → sem.Decodes proposition tuple →
      ∃ contribution, contribution ∈ plan.tuples ∧
        contribution.proposition = proposition ∧ contribution.tuple = tuple

end InspectionPlan

/-- Evidence for `Γ ; e ⊢extract K`: a sound IYKYK knowledge snapshot and a finite inventory
of owned contributions, complete for applicable exposures and decodable retained propositions. -/
public structure Extraction {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    (sem : Semantics World L base context) (program : Program L) {KnowledgeRoot : Type x}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot) {sort : Ty}
    (expression : Term L sort) where
  knowledgeSound : knowledge.Sound context
  plan : InspectionPlan sem program knowledge expression
  complete : plan.Complete

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
    ((Trace.unions (plan.witnesses.map WitnessContribution.trace)).union
      ((Trace.unions (plan.computations.map ComputationContribution.trace)).union
        ((Trace.unions (plan.exposures.map ExposureContribution.trace)).union
          (Trace.unions (plan.tuples.map KnowledgeContribution.trace)))))

/-- Compose an extracted snapshot with the concrete relational inspection rules. -/
@[expose] public def Extraction.inspect
    {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
    {context : Iykyk.Metatheory.Context World} {sem : Semantics World L base context}
    {program : Program L} {KnowledgeRoot : Type x}
    {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot} {sort : Ty}
    {expression : Term L sort} (extraction : Extraction sem program knowledge expression) :
    Trace context sem.model :=
  SpytialLean.Semantics.inspect sem program knowledge expression extraction.plan

end SpytialLean.Semantics

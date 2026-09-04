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
an equality from checked IYKYK knowledge. Both then run the same defined structural walk
`Semantics.walkFrom` over `v`, rooted at the atom for `e`, and record the exposure in the trace.

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
  /-- EXPOSE-PROOF: checked knowledge contains the equality `expression = value`. -/
  | proof {value}
      (known : equalityFact (sem.denote expression) (sem.denote value) ∈ knowledge.facts) :
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

end SpytialLean.Semantics

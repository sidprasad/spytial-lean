module

public import Relational

public section

/-!
# Inspection by computation and proof

The selected expression and every value exposed from it are typed semantic atoms. Computation may
expose a value equal to the expression. A checked fact in IYKYK knowledge may establish the same
equality, or it may directly justify a relational tuple. All three cases produce the same kind of
relational instance.
-/

namespace SpytialLean.Semantics

universe u v w

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

/-- The semantic result of evaluating an expression far enough to expose a value. -/
public abbrev ComputesTo {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {sort : Ty}
    (expression value : Atom context model sort) := EqualInContext expression value

/-- A value may be exposed either by computation or by an equality retained in checked knowledge. -/
public inductive Resolution {World : Type u} {Ty : Type v} {KnowledgeRoot : Type w}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {rootSort : Ty}
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot)
    (expression : Atom context model rootSort) : Atom context model rootSort → Prop where
  | computation {value} (computes : ComputesTo expression value) :
      Resolution knowledge expression value
  | proof {value} (known : equalityFact expression value ∈ knowledge.facts) :
      Resolution knowledge expression value

/-- Ordinary structural relationalization at the semantic boundary. -/
public abbrev StructuralRelationalizer {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    (model : Model World signature) (rootSort : Ty) :=
  Atom context model rootSort → Instance context model

/-- The explicit assumption inherited from ordinary Spytial relationalization. -/
@[expose] public def StructuralSound {World : Type u} {Ty : Type v}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {rootSort : Ty}
    (relationalize : StructuralRelationalizer (context := context) model rootSort) : Prop :=
  ∀ value, (relationalize value).Sound

/--
The inspection judgment. It contains only the rules needed by the central claim:

* retain an opaque term as an atom;
* inspect structure exposed by computation or proof;
* report a tuple backed by checked knowledge; and
* combine independently justified observations.
-/
public inductive Inspection {World : Type u} {Ty : Type v} {KnowledgeRoot : Type w}
    {context : Iykyk.Metatheory.Context World} {signature : Signature Ty}
    {model : Model World signature} {rootSort : Ty}
    (relationalize : StructuralRelationalizer (context := context) model rootSort)
    (knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot)
    (expression : Atom context model rootSort) : Instance context model → Prop where
  | opaqueTerm : Inspection relationalize knowledge expression (Instance.ofAtom expression)
  | resolved {value} (resolution : Resolution knowledge expression value) :
      Inspection relationalize knowledge expression (relationalize value)
  | proved {tuple : Tuple signature (Atom context model)}
      (known : tuple.fact ∈ knowledge.facts) :
      Inspection relationalize knowledge expression (Instance.ofTuple tuple)
  | combine {left right}
      (leftInspection : Inspection relationalize knowledge expression left)
      (rightInspection : Inspection relationalize knowledge expression right) :
      Inspection relationalize knowledge expression (left.union right)

end SpytialLean.Semantics

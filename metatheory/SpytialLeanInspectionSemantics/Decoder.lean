module

public import SpytialLeanInspectionSemantics.Structural

public section

/-!
# Checked proposition decoding

`Proposition` is the small, explicit boundary with the production `Lean.Expr` decoder. A direct
predicate reaches this layer only after its head resolves to a relation in `base` and its retained
arguments check against that relation's columns. An equation reaches it with intrinsically typed
terms; `decode` accepts it only when either side is a named operation application. Negations and
unresolved disjunctions remain propositions but do not decode to unconditional positive tuples.

The production parser is responsible only for constructing this checked shape. Relation and graph
meanings are fixed here, and `decode_sound` proves the semantic bridge once for every accepted
shape. A contribution therefore needs a checked proposition and successful decoding, never a
separate proposition-implies-tuple premise.
-/

namespace SpytialLean.Semantics

universe u v w x

/-- The checked proposition shapes at the boundary of the owned Lean-expression decoder. -/
public inductive Proposition {Ty : Type u} (L : Language.{u, v} Ty)
    (base : Signature.{u, v} Ty) : Type (max (u + 1) (v + 1)) where
  | relation (symbol : base.Relation)
      (arguments : Arguments (Term L) (base.columns symbol))
  | equation {sort : Ty} (left right : Term L sort)
  | negative (proposition : Proposition L base)
  | disjunction (left right : Proposition L base)

namespace Proposition

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World}

/-- Meaning of a checked proposition at one context-compatible world. -/
@[expose] public def Holds (sem : Semantics World L base context) :
    Proposition L base → (world : World) → context world → Prop
  | .relation symbol arguments, world, compatible =>
      sem.holds world symbol (sem.denoteArgs arguments world compatible)
  | .equation left right, world, compatible =>
      sem.denote left world compatible = sem.denote right world compatible
  | .negative proposition, world, compatible => ¬ proposition.Holds sem world compatible
  | .disjunction left right, world, compatible =>
      left.Holds sem world compatible ∨ right.Holds sem world compatible

/-- The IYKYK fact corresponding to a checked proposition. -/
@[expose] public def fact (sem : Semantics World L base context)
    (proposition : Proposition L base) : Iykyk.Metatheory.Fact World :=
  fun world => ∀ compatible : context world, proposition.Holds sem world compatible

end Proposition

namespace Semantics

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World}

/-- A checked direct relation application interpreted as a tuple. -/
@[expose] public def relationTuple (sem : Semantics World L base context)
    (symbol : base.Relation) (arguments : Arguments (Term L) (base.columns symbol)) :
    Tuple (base.withFields L) (Atom context sem.model) where
  relation := .inl symbol
  arguments := arguments.map sem.denote

/-- Try the symmetric graph orientation after the left side was not an operation. -/
@[expose] public def decodeRightGraph (sem : Semantics World L base context) {sort : Ty}
    (left : Term L sort) :
    (right : Term L sort) → Option (Tuple (base.withFields L) (Atom context sem.model))
  | .op operation arguments => some (sem.graphTuple operation arguments left)
  | _ => none

/-- Decode only the supported orientations of a typed equation. -/
@[expose] public def decodeEquation (sem : Semantics World L base context) {sort : Ty}
    (left right : Term L sort) : Option (Tuple (base.withFields L) (Atom context sem.model)) :=
  match left with
  | .var name => sem.decodeRightGraph (.var name) right
  | .con constructor arguments => sem.decodeRightGraph (.con constructor arguments) right
  | .op operation arguments => some (sem.graphTuple operation arguments right)

/-- The owned checked decoder. Its result is well typed by construction. -/
@[expose] public def decode (sem : Semantics World L base context) :
    Proposition L base → Option (Tuple (base.withFields L) (Atom context sem.model))
  | .relation symbol arguments => some (sem.relationTuple symbol arguments)
  | .equation left right => sem.decodeEquation left right
  | .negative _ => none
  | .disjunction _ _ => none

/-- The decoder relation used by inspection rules. -/
@[expose] public def Decodes (sem : Semantics World L base context)
    (proposition : Proposition L base)
    (tuple : Tuple (base.withFields L) (Atom context sem.model)) : Prop :=
  sem.decode proposition = some tuple

/-- Direct predicates retain their resolved relation head and typed arguments exactly. -/
@[simp] public theorem decode_relation (sem : Semantics World L base context)
    (symbol : base.Relation) (arguments : Arguments (Term L) (base.columns symbol)) :
    sem.decode (.relation symbol arguments) = some (sem.relationTuple symbol arguments) :=
  rfl

/-- A term in a direct predicate remains the same semantic atom in the decoded tuple. -/
public theorem relationTuple_contains_term (sem : Semantics World L base context)
    {symbol : base.Relation} {arguments : Arguments (Term L) (base.columns symbol)}
    {position : Nat} {sort : Ty} {term : Term L sort}
    (occurs : arguments.At position term) :
    TypedAtom.mk sort (sem.denote term) ∈ (sem.relationTuple symbol arguments).atoms :=
  (occurs.map sem.denote).mem_atoms

/-- A named application on the left becomes a function-graph point. -/
@[simp] public theorem decode_graph_left (sem : Semantics World L base context)
    (operation : L.Op) (arguments : Arguments (Term L) (L.params operation))
    (result : Term L (L.opResult operation)) :
    sem.decode (.equation (.op operation arguments) result) =
      some (sem.graphTuple operation arguments result) :=
  rfl

@[simp] public theorem decode_negative (sem : Semantics World L base context)
    (proposition : Proposition L base) : sem.decode (.negative proposition) = none :=
  rfl

@[simp] public theorem decode_disjunction (sem : Semantics World L base context)
    (left right : Proposition L base) : sem.decode (.disjunction left right) = none :=
  rfl

/-- Soundness of the symmetric graph orientation. -/
public theorem decodeRightGraph_sound (sem : Semantics World L base context) {sort : Ty}
    (left : Term L sort) : ∀ {right : Term L sort}
      {tuple : Tuple (base.withFields L) (Atom context sem.model)},
      sem.decodeRightGraph left right = some tuple → ∀ {world : World}
        {compatible : context world},
        sem.denote left world compatible = sem.denote right world compatible ↔
          tuple.Holds world compatible
  | .var _, _, decoded => by simp [decodeRightGraph] at decoded
  | .con _ _, _, decoded => by simp [decodeRightGraph] at decoded
  | .op operation arguments, tuple, decoded => by
      simp only [decodeRightGraph, Option.some.injEq] at decoded
      subst tuple
      constructor
      · intro equal
        exact sem.graphTuple_holds_iff.mpr equal.symm
      · intro holds
        exact (sem.graphTuple_holds_iff.mp holds).symm

/-- Soundness of the equation sub-decoder, including symmetric orientation. -/
public theorem decodeEquation_sound (sem : Semantics World L base context) {sort : Ty} :
    ∀ {left right : Term L sort}
      {tuple : Tuple (base.withFields L) (Atom context sem.model)},
      sem.decodeEquation left right = some tuple → ∀ {world : World}
        {compatible : context world},
        sem.denote left world compatible = sem.denote right world compatible ↔
          tuple.Holds world compatible
  | .var _, right, _, decoded => sem.decodeRightGraph_sound _ decoded
  | .con _ _, right, _, decoded => sem.decodeRightGraph_sound _ decoded
  | .op operation arguments, right, tuple, decoded => by
      simp only [decodeEquation, Option.some.injEq] at decoded
      subst tuple
      exact sem.graphTuple_holds_iff.symm

/-- Every accepted proposition shape has exactly the meaning of its emitted tuple. -/
public theorem decode_sound (sem : Semantics World L base context)
    {proposition : Proposition L base}
    {tuple : Tuple (base.withFields L) (Atom context sem.model)}
    (decoded : sem.Decodes proposition tuple) {world : World} {compatible : context world} :
    proposition.Holds sem world compatible ↔ tuple.Holds world compatible := by
  cases proposition with
  | relation symbol arguments =>
      simp only [Decodes, decode, Option.some.injEq] at decoded
      subst tuple
      change sem.holds world symbol (sem.denoteArgs arguments world compatible) ↔
        sem.holds world symbol
          ((arguments.map sem.denote).map (fun atom => atom world compatible))
      rw [map_denote]
  | equation left right => exact sem.decodeEquation_sound decoded
  | negative proposition => simp [Decodes, decode] at decoded
  | disjunction left right => simp [Decodes, decode] at decoded

/-- A kernel-checked IYKYK fact and successful decoding suffice to prove the emitted tuple. -/
public theorem checked_decode_holds (sem : Semantics World L base context)
    {KnowledgeRoot : Type x} {knowledge : Iykyk.Metatheory.Knowledge World KnowledgeRoot}
    {proposition : Proposition L base}
    {tuple : Tuple (base.withFields L) (Atom context sem.model)}
    (knowledgeSound : knowledge.Sound context)
    (known : proposition.fact sem ∈ knowledge.facts) (decoded : sem.Decodes proposition tuple)
    (world : World) (compatible : context world) : tuple.Holds world compatible :=
  (sem.decode_sound decoded).mp (knowledgeSound known world compatible compatible)

end Semantics

end SpytialLean.Semantics

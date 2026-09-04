module

public import SpytialLeanInspectionSemantics.Relational

public section

/-!
# Terms, evaluation, and structural relationalization

This file gives the core fragment of Spytial's structural walk a syntax and a meaning:

* `Term` is the fragment the walk understands: opaque variables, constructor applications, and
  applications of defined operations.
* `Eval` is a big-step operational semantics. It is a relation on syntax, not contextual equality.
  Computation happens only where a `Program` rule fires.
* `Field` is the vocabulary of generated field relations. `Semantics.model` fixes the meaning of
  `field C i` as the `i`-th constructor projection of `C`.
* `walkFrom` is the recursive structural relationalizer. It is a definition, not a parameter.

What is not modelled: Lean's actual reduction, binders and substitution inside rules, custom
relationalizers, and presentation names for relations and atoms.
-/

namespace SpytialLean.Semantics

universe u v w

/-- Why a constructor argument is or is not drawn. Only `data` arguments produce field tuples. -/
public inductive BinderRole where
  | typeParameter
  | instanceParameter
  | proof
  | data
  deriving DecidableEq

/-- The syntax of the core fragment: constructors with their argument sorts and drawing policy,
defined operations, and typed variables standing for terms whose structure the walk cannot see. -/
public structure Language (Ty : Type u) where
  Constructor : Type v
  result : Constructor → Ty
  binders : Constructor → List Ty
  /-- The drawing policy for the argument of a constructor at a position. -/
  role : Constructor → Nat → BinderRole
  Op : Type v
  params : Op → List Ty
  opResult : Op → Ty
  Var : Ty → Type v

/-- Intrinsically typed terms of the core fragment. -/
public inductive Term {Ty : Type u} (L : Language.{u, v} Ty) : Ty → Type (max u v) where
  | var {sort} (x : L.Var sort) : Term L sort
  | con (C : L.Constructor) (args : Arguments (Term L) (L.binders C)) : Term L (L.result C)
  | op (f : L.Op) (args : Arguments (Term L) (L.params f)) : Term L (L.opResult f)

/-- The reduction rules of the defined operations. Given evaluated arguments, `rule` returns the
right-hand side to continue evaluating, or `none` when no rule applies and the application is
stuck. This is the only place computation happens. -/
public structure Program {Ty : Type u} (L : Language.{u, v} Ty) where
  rule : (f : L.Op) → Arguments (Term L) (L.params f) → Option (Term L (L.opResult f))

mutual
/-- Big-step evaluation `e -->op v`. Variables are values, constructor applications evaluate
their arguments, and an operation evaluates its arguments, fires a rule, and continues; a
stuck application is its own residual. -/
public inductive Eval {Ty : Type u} {L : Language.{u, v} Ty} (program : Program L) :
    {sort : Ty} → Term L sort → Term L sort → Prop where
  | var {sort} (x : L.Var sort) : Eval program (.var x) (.var x)
  | con {C args vals} (fields : EvalArgs program args vals) :
      Eval program (.con C args) (.con C vals)
  | op {f args vals body value} (fields : EvalArgs program args vals)
      (fires : program.rule f vals = some body) (rest : Eval program body value) :
      Eval program (.op f args) value
  | stuck {f args vals} (fields : EvalArgs program args vals)
      (blocked : program.rule f vals = none) :
      Eval program (.op f args) (.op f vals)
/-- Pointwise evaluation of an argument list. -/
public inductive EvalArgs {Ty : Type u} {L : Language.{u, v} Ty} (program : Program L) :
    {sorts : List Ty} → Arguments (Term L) sorts → Arguments (Term L) sorts → Prop where
  | nil : EvalArgs program .nil .nil
  | cons {sort sorts} {head value : Term L sort} {tail vals : Arguments (Term L) sorts}
      (first : Eval program head value) (rest : EvalArgs program tail vals) :
      EvalArgs program (.cons head tail) (.cons value vals)
end

/-- The relation symbol for the argument at `position` of `constructor`, of the given sort. -/
public structure Field {Ty : Type u} (L : Language.{u, v} Ty) where
  constructor : L.Constructor
  position : Nat
  sort : Ty

/-- Extend a vocabulary with one field relation per constructor position. -/
@[expose] public def Signature.withFields {Ty : Type u} (base : Signature Ty)
    (L : Language.{u, v} Ty) : Signature Ty where
  Relation := base.Relation ⊕ Field L
  columns
    | .inl relation => base.columns relation
    | .inr field => [L.result field.constructor, field.sort]

namespace Arguments

/-- `args.At position entry`: the argument at `position` is `entry`. -/
public inductive At {Ty : Type u} {Entry : Ty → Type v} :
    {sorts : List Ty} → Arguments Entry sorts → Nat → {sort : Ty} → Entry sort → Prop where
  | here {sort sorts} {head : Entry sort} {tail : Arguments Entry sorts} :
      At (.cons head tail) 0 head
  | there {sort sorts} {head : Entry sort} {tail : Arguments Entry sorts} {position : Nat}
      {sort' : Ty} {entry : Entry sort'} (rest : At tail position entry) :
      At (.cons head tail) (position + 1) entry

/-- `IsDrop position full rest`: `rest` is `full` with its first `position` arguments removed. -/
public inductive IsDrop {Ty : Type u} {Entry : Ty → Type v} :
    Nat → {full rest : List Ty} → Arguments Entry full → Arguments Entry rest → Prop where
  | zero {sorts} {args : Arguments Entry sorts} : IsDrop 0 args args
  | succ {sort sorts rest} {head : Entry sort} {tail : Arguments Entry sorts}
      {remaining : Arguments Entry rest} {position : Nat} (drop : IsDrop position tail remaining) :
      IsDrop (position + 1) (.cons head tail) remaining

/-- The head of a suffix at `position` is the argument at `position`. -/
public theorem IsDrop.at {Ty : Type u} {Entry : Ty → Type v} :
    ∀ {position : Nat} {full : List Ty} {sort : Ty} {sorts : List Ty}
      {args : Arguments Entry full} {head : Entry sort} {tail : Arguments Entry sorts},
      IsDrop position args (.cons head tail) → args.At position head
  | _, _, _, _, _, _, _, .zero => .here
  | _, _, _, _, _, _, _, .succ drop => .there (IsDrop.at drop)

/-- Dropping one more argument from a suffix. -/
public theorem IsDrop.tail {Ty : Type u} {Entry : Ty → Type v} :
    ∀ {position : Nat} {full : List Ty} {sort : Ty} {sorts : List Ty}
      {args : Arguments Entry full} {head : Entry sort} {tail : Arguments Entry sorts},
      IsDrop position args (.cons head tail) → IsDrop (position + 1) args tail
  | _, _, _, _, _, _, _, .zero => .succ .zero
  | _, _, _, _, _, _, _, .succ drop => .succ (IsDrop.tail drop)

end Arguments

/-- The meaning of the core fragment in the worlds allowed by a context: carriers, constructor
and operation functions, values for variables, and the meaning of the base relations. -/
public structure Semantics (World : Type w) {Ty : Type u} (L : Language.{u, v} Ty)
    (base : Signature Ty) (context : Iykyk.Metatheory.Context World) where
  Carrier : Ty → Type (max u w)
  constructor : (C : L.Constructor) → Arguments Carrier (L.binders C) → Carrier (L.result C)
  operation : (f : L.Op) → Arguments Carrier (L.params f) → Carrier (L.opResult f)
  var : ∀ {sort : Ty}, L.Var sort → (world : World) → context world → Carrier sort
  holds : (world : World) → (relation : base.Relation) →
    Arguments Carrier (base.columns relation) → Prop

namespace Semantics

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World}

/-- The fixed meaning of a field relation: `field C i` relates `C(args)` to the argument at
position `i`. This is the semantic contract of every generated field tuple. -/
@[expose] public def fieldHolds (sem : Semantics World L base context) (field : Field L) :
    Arguments sem.Carrier [L.result field.constructor, field.sort] → Prop
  | .cons owner (.cons child .nil) =>
      ∃ args, owner = sem.constructor field.constructor args ∧ args.At field.position child

/-- The relational model over the base vocabulary extended with field relations. -/
@[expose] public def model (sem : Semantics World L base context) :
    Model World (base.withFields L) where
  Carrier := sem.Carrier
  holds world
    | .inl relation, args => sem.holds world relation args
    | .inr field, args => sem.fieldHolds field args

mutual
/-- The typed atom denoted by a term. Two occurrences of one typed term denote one atom, which is
how the walk reuses atoms for repeated terms. -/
@[expose] public def denote (sem : Semantics World L base context) :
    {sort : Ty} → Term L sort → Atom context sem.model sort
  | _, .var x, world, compatible => sem.var x world compatible
  | _, .con C args, world, compatible =>
      sem.constructor C (sem.denoteArgs args world compatible)
  | _, .op f args, world, compatible =>
      sem.operation f (sem.denoteArgs args world compatible)
/-- The denotations of an argument list. -/
@[expose] public def denoteArgs (sem : Semantics World L base context) :
    {sorts : List Ty} → Arguments (Term L) sorts →
    (world : World) → context world → Arguments sem.Carrier sorts
  | _, .nil, _, _ => .nil
  | _, .cons head tail, world, compatible =>
      .cons (sem.denote head world compatible) (sem.denoteArgs tail world compatible)
end

/-- The semantics validates the program: whenever a rule fires, the operation applied to the
argument denotations is the denotation of the right-hand side. This is the assumption that
evaluation computes the intended meaning; in Lean it is played by the kernel. -/
@[expose] public def Implements (sem : Semantics World L base context) (program : Program L) :
    Prop :=
  ∀ (f : L.Op) (args : Arguments (Term L) (L.params f)) (body : Term L (L.opResult f)),
    program.rule f args = some body →
      ∀ world (compatible : context world),
        sem.operation f (sem.denoteArgs args world compatible) = sem.denote body world compatible

end Semantics

mutual
/-- Evaluation preserves denotation in every compatible world. -/
public theorem Eval.sound {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    {sem : Semantics World L base context} {program : Program L}
    (implements : sem.Implements program) :
    ∀ {sort : Ty} {expression value : Term L sort}, Eval program expression value →
      ∀ world (compatible : context world),
        sem.denote expression world compatible = sem.denote value world compatible
  | _, _, _, .var _, _, _ => rfl
  | _, _, _, .con fields, world, compatible => by
      simp only [Semantics.denote]
      rw [EvalArgs.sound implements fields world compatible]
  | _, _, _, .op fields fires rest, world, compatible => by
      simp only [Semantics.denote]
      rw [EvalArgs.sound implements fields world compatible,
        implements _ _ _ fires world compatible, Eval.sound implements rest world compatible]
  | _, _, _, .stuck fields _, world, compatible => by
      simp only [Semantics.denote]
      rw [EvalArgs.sound implements fields world compatible]
/-- Pointwise evaluation preserves the denotations of an argument list. -/
public theorem EvalArgs.sound {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty}
    {base : Signature Ty} {context : Iykyk.Metatheory.Context World}
    {sem : Semantics World L base context} {program : Program L}
    (implements : sem.Implements program) :
    ∀ {sorts : List Ty} {args vals : Arguments (Term L) sorts}, EvalArgs program args vals →
      ∀ world (compatible : context world),
        sem.denoteArgs args world compatible = sem.denoteArgs vals world compatible
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons first rest, world, compatible => by
      simp only [Semantics.denoteArgs]
      rw [Eval.sound implements first world compatible,
        EvalArgs.sound implements rest world compatible]
end

namespace Semantics

variable {World : Type w} {Ty : Type u} {L : Language.{u, v} Ty} {base : Signature Ty}
  {context : Iykyk.Metatheory.Context World}

/-- The tuple relating an owner atom to its field atom. Its typing is fixed by the field symbol. -/
@[expose] public def fieldTuple (sem : Semantics World L base context) (C : L.Constructor)
    (position : Nat) {sort : Ty} (owner : Atom context sem.model (L.result C))
    (child : Atom context sem.model sort) : Tuple (base.withFields L) (Atom context sem.model) where
  relation := .inr ⟨C, position, sort⟩
  arguments := .cons owner (.cons child .nil)

mutual
/-- The recursive structural relationalizer, rooted at a given atom for the term.

A variable or a stuck application is one opaque atom. A constructor application keeps the root
atom, emits a field tuple from the root to each `data` argument, and relationalizes those
arguments from their own denotations. Arguments with any other `BinderRole` are omitted. -/
@[expose] public def walkFrom (sem : Semantics World L base context) :
    {sort : Ty} → Term L sort → Atom context sem.model sort → Instance context sem.model
  | _, .var _, root => Instance.ofAtom root
  | _, .con C args, root => (Instance.ofAtom root).union (sem.walkFields C 0 root args)
  | _, .op _ _, root => Instance.ofAtom root
/-- Walk the arguments of `C` starting at `position`, owned by `owner`. -/
@[expose] public def walkFields (sem : Semantics World L base context) (C : L.Constructor) :
    Nat → Atom context sem.model (L.result C) → {sorts : List Ty} → Arguments (Term L) sorts →
    Instance context sem.model
  | _, _, _, .nil => Instance.empty
  | position, owner, _, .cons head tail =>
      let here :=
        if L.role C position = .data then
          (Instance.ofTuple (sem.fieldTuple C position owner (sem.denote head))).union
            (sem.walkFrom head (sem.denote head))
        else Instance.empty
      here.union (sem.walkFields C (position + 1) owner tail)
end

/-- Ordinary structural relationalization of a term: the walk rooted at the term's own atom. -/
@[expose] public def relationalize (sem : Semantics World L base context) {sort : Ty}
    (term : Term L sort) : Instance context sem.model :=
  sem.walkFrom term (sem.denote term)

/-- A field tuple holds when the owner is `C` applied to arguments whose entry at `position` is
the child. This is the only fact the walk ever needs about a field relation. -/
public theorem fieldTuple_holds (sem : Semantics World L base context) {C : L.Constructor}
    {position : Nat} {sort : Ty} {owner : Atom context sem.model (L.result C)}
    {child : Atom context sem.model sort} {world : World} {compatible : context world}
    (args : Arguments sem.Carrier (L.binders C))
    (owns : owner world compatible = sem.constructor C args)
    (at_ : args.At position (child world compatible)) :
    (sem.fieldTuple C position owner child).Holds world compatible :=
  ⟨args, owns, at_⟩

mutual
/-- Every field tuple of the walk holds, provided the root denotes the term. -/
public theorem walkFrom_sound (sem : Semantics World L base context) :
    ∀ {sort : Ty} (term : Term L sort) (root : Atom context sem.model sort),
      (∀ world (compatible : context world),
        root world compatible = sem.denote term world compatible) →
      (sem.walkFrom term root).Sound
  | _, .var _, root, _ => by
      simp only [walkFrom]
      exact Instance.sound_ofAtom root
  | _, .con C args, root, denotes => by
      simp only [walkFrom]
      refine Instance.sound_union (Instance.sound_ofAtom root)
        (sem.walkFields_sound C 0 root args fun world compatible => ?_)
      exact ⟨sem.denoteArgs args world compatible, denotes world compatible, .zero⟩
  | _, .op _ _, root, _ => by
      simp only [walkFrom]
      exact Instance.sound_ofAtom root
/-- Every field tuple of the argument walk holds, provided the owner denotes `C` applied to a
list of which the remaining arguments are the suffix at `position`. -/
public theorem walkFields_sound (sem : Semantics World L base context) (C : L.Constructor) :
    ∀ (position : Nat) (owner : Atom context sem.model (L.result C)) {sorts : List Ty}
      (args : Arguments (Term L) sorts),
      (∀ world (compatible : context world), ∃ full : Arguments sem.Carrier (L.binders C),
        owner world compatible = sem.constructor C full ∧
          Arguments.IsDrop position full (sem.denoteArgs args world compatible)) →
      (sem.walkFields C position owner args).Sound
  | _, _, _, .nil, _ => by
      simp only [walkFields]
      exact Instance.sound_empty
  | position, owner, _, .cons head tail, owns => by
      simp only [walkFields]
      refine Instance.sound_union ?_ (sem.walkFields_sound C (position + 1) owner tail ?_)
      · split
        · refine Instance.sound_union (Instance.sound_ofTuple _ ?_)
            (sem.walkFrom_sound head (sem.denote head) fun _ _ => rfl)
          intro world compatible
          obtain ⟨full, owns, drop⟩ := owns world compatible
          exact sem.fieldTuple_holds full owns (Arguments.IsDrop.at drop)
        · exact Instance.sound_empty
      · intro world compatible
        obtain ⟨full, owns, drop⟩ := owns world compatible
        exact ⟨full, owns, Arguments.IsDrop.tail drop⟩
end

mutual
/-- Every tuple emitted by the walk is a field tuple at a `data` position. The walk is therefore
well typed by construction: the owner atom has the constructor's result sort and the child atom
has the sort recorded in the field symbol. -/
public theorem walkFrom_tuples (sem : Semantics World L base context) :
    ∀ {sort : Ty} (term : Term L sort) (root : Atom context sem.model sort)
      (tuple : Tuple (base.withFields L) (Atom context sem.model)),
      tuple ∈ (sem.walkFrom term root).tuples →
      ∃ (C : L.Constructor) (position : Nat) (sort' : Ty)
        (owner : Atom context sem.model (L.result C)) (child : Atom context sem.model sort'),
        L.role C position = .data ∧ tuple = sem.fieldTuple C position owner child
  | _, .var _, _, _, present => by
      simp [walkFrom, Instance.ofAtom] at present
  | _, .con C args, root, tuple, present => by
      simp only [walkFrom, Instance.union, Instance.ofAtom, List.nil_append] at present
      exact sem.walkFields_tuples C 0 root args tuple present
  | _, .op _ _, _, _, present => by
      simp [walkFrom, Instance.ofAtom] at present
/-- Every tuple emitted by the argument walk is a field tuple at a `data` position. -/
public theorem walkFields_tuples (sem : Semantics World L base context) (C : L.Constructor) :
    ∀ (position : Nat) (owner : Atom context sem.model (L.result C)) {sorts : List Ty}
      (args : Arguments (Term L) sorts) (tuple : Tuple (base.withFields L) (Atom context sem.model)),
      tuple ∈ (sem.walkFields C position owner args).tuples →
      ∃ (C' : L.Constructor) (position' : Nat) (sort' : Ty)
        (owner' : Atom context sem.model (L.result C')) (child : Atom context sem.model sort'),
        L.role C' position' = .data ∧ tuple = sem.fieldTuple C' position' owner' child
  | _, _, _, .nil, _, present => by
      simp [walkFields, Instance.empty] at present
  | position, owner, _, .cons head tail, tuple, present => by
      simp only [walkFields, Instance.union, List.mem_append] at present
      rcases present with here | there
      · split at here
        · simp only [Instance.ofTuple, List.mem_append, List.mem_singleton] at here
          rcases here with rfl | inner
          · exact ⟨C, position, _, owner, sem.denote head, ‹L.role C position = .data›, rfl⟩
          · exact sem.walkFrom_tuples head (sem.denote head) tuple inner
        · simp [Instance.empty] at here
      · exact sem.walkFields_tuples C (position + 1) owner tail tuple there
end

/-- Ordinary relationalization is sound: the root is the term's own denotation. -/
public theorem relationalize_sound (sem : Semantics World L base context) {sort : Ty}
    (term : Term L sort) : (sem.relationalize term).Sound :=
  sem.walkFrom_sound term (sem.denote term) fun _ _ => rfl

end Semantics

end SpytialLean.Semantics

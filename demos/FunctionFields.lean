import SpytialLean

open SpytialLean

/-! # Function Fields

Structures with function-valued fields should decompose into mapping
graphs rather than rendering as opaque lambda blobs.

## Two views of a function: extensional vs intensional

The relationalizer renders a `λ` two different ways depending on its domain:

* **Extensional (what it computes).** When the domain is *finite and
  enumerable* (`Bool`, `Fin n` for `n ≤ 20`, a zero-arity enum inductive), the
  walker enumerates every input and emits one edge per input→output pair. The
  diagram *is* the function's graph. This is the default and its shape is fixed.

* **Intensional (how it is defined).** When the domain is *not* enumerable
  (`Nat`, `List Nat`, …), enumerating is impossible, so instead of an opaque
  leaf the walker decomposes the function *body* structurally — an AST view.
  Entering the binder with `withLocalDecl`, it weak-head-reduces the body
  (without unfolding definitions or `let`s) and emits:

  - `if` / `dite` → an `if` node with `condition` / `then` / `else` edges,
  - a pattern match (matcher auxiliary or `casesOn`) → a `match` node with a
    `match` edge to the discriminant and one edge per branch, labeled by the
    matching constructor,
  - `let` → a `let` node with `let_value` / `let_body` edges,
  - nested `λ` (multi-argument functions) → a `body` edge into the next binder,
  - anything else (the bound variable, arithmetic on it, …) → a leaf labeled
    with the pretty-printed surface expression (`n * 2`, `n > 10`).

  Nested constructs nest: the `then` branch of an `if` can itself be an `if`.
-/

/-! ## Lightweight category theory structures -/

/-- A simple "objects + morphisms" container. -/
structure HomStruct where
  obj : Type
  hom : obj → obj → Type

/-- A functor between two HomStructs — `obj` is a function-valued field. -/
structure SimpleFunctor (C D : HomStruct) where
  obj : C.obj → D.obj

/-! ## Concrete instances using finite types -/

inductive ThreeObj where | a | b | c
  deriving Repr

inductive TwoObj where | x | y
  deriving Repr

def threeStruct : HomStruct := { obj := ThreeObj, hom := fun _ _ => Unit }
def twoStruct : HomStruct := { obj := TwoObj, hom := fun _ _ => Unit }

def myObjMap : ThreeObj → TwoObj
  | .a => .x
  | .b => .y
  | .c => .x

def myFunctor : SimpleFunctor threeStruct twoStruct :=
  { obj := myObjMap }

-- This should show a mapping graph: myObjMap node with edges a→x, b→y, c→x
-- Before the fix, this renders `obj` as an opaque lambda blob.
#spytial myFunctor


/-! ## Simple transform example -/

structure Transform where
  f : Bool → Nat

def myTransform : Transform :=
  { f := fun b => if b then 42 else 0 }

-- `f` has a finite domain (`Bool`) — extensional view: enumerate true→42,
-- false→0. The body `if b then …` is NOT decomposed structurally here, because
-- enumeration already shows exactly what the function computes.
#spytial myTransform

/-! ## Non-finite function field — structural (AST) decomposition

`Nat` is not enumerable, so `process` cannot be shown extensionally. Rather than
the opaque lambda blob this used to render, the body is now decomposed into an
AST: `Processor.mk` → `process` → `λ n` → `body` → leaf `n + 1`. -/

structure Processor where
  process : Nat → Nat

def myProcessor : Processor :=
  { process := fun n => n + 1 }

#spytial myProcessor
#spytial.datum myProcessor

/-! ## Structural decomposition gallery (intensional view)

The functions below all have non-enumerable domains, so each is shown as the
structure of its definition. Use `#spytial.datum` to inspect the JSON: the
`if` / `match` / `let` nodes and their edges are visible there. -/

/-- An `if`-expression body. The decidable condition `n > 10` does not block the
    `ite` — the walker emits an `if` node with `condition` / `then` / `else`
    edges to the leaves `n > 10`, `n * 2`, `n + 1`. -/
def classify : Nat → Nat := fun n => if n > 10 then n * 2 else n + 1

#spytial classify
#spytial.datum classify

/-- Nested `if`: the `then` branch is itself an `if`, so the diagram nests one
    `if` node inside another's `then` edge. -/
def bucket : Nat → Nat := fun n =>
  if n > 100 then 3 else if n > 10 then 2 else 1

#spytial bucket
#spytial.datum bucket

/-- A pattern match over `List Nat` (a non-finite inductive payload). `match`
    compiles to a matcher auxiliary; the walker emits a `match` node, a `match`
    edge to the discriminant `l`, and `nil` / `cons` branch edges. -/
def headOrZero : List Nat → Nat := fun l =>
  match l with
  | [] => 0
  | x :: _ => x

#spytial headOrZero
#spytial.datum headOrZero

/-- A two-argument function: nested lambdas decompose one binder per layer.
    `λ a` → `body` → `λ b` → `body` → leaf `a + b`. -/
def add2 : Nat → Nat → Nat := fun a b => a + b

#spytial add2
#spytial.datum add2

/-- A `let`-binding survives reduction (zeta is disabled), so it surfaces as a
    `let` node with `let_value` and `let_body` edges; the body here is itself an
    `if`, which nests under `let_body`. -/
def stepThenBranch : Nat → Nat := fun n =>
  let y := n + 1
  if y > 5 then y else 0

#spytial stepThenBranch
#spytial.datum stepThenBranch

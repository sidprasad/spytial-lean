import SpytialLean

open SpytialLean

/-! # Proof-state diagrams (`spytial.state`)

In proof mode you often have a value you don't fully know. There are two
kinds of holes:

1. **Opaque hole** — all you know is the type. `t : DTree` in the context, or
   an untouched metavariable. It draws as one atom of that type.
2. **Structured hole** — you know more than the type. The extra knowledge
   comes from the elaborator (a `refine` partially built the term) or from
   the hypotheses (`h : t = node l r` says what `t` is; `h : t ≠ leaf 0`
   says what it is not).

`spytial.state` renders the main goal — its hypotheses and its target — so
both kinds are visible. One diagram is one goal: sibling goals (the branches
of a `cases`) assume contradictory things about the same variables, so each
gets its own picture — put `spytial.state` inside the branch you want to see.

Tactics run during elaboration, so `lake build Demos` exercises everything
below; the `.datum` variants print their JSON to the build log, which is the
headless verification mechanism. -/

inductive DTree where
  | leaf (value : Nat)
  | node (left right : DTree)
  deriving DecidableEq

/-! ## 1. An opaque hole

`t` is an abstract variable: no constructor structure to descend into, so it
renders as a single `DTree`-typed atom labeled `t`. -/

set_option linter.unusedVariables false in
example (t : DTree) : True := by
  spytial.state
  trivial

/-! ## 2. The elaborator knows structure

After `refine ⟨DTree.node ?l ?r, ?h⟩` the witness is the partially-built term
`DTree.node ?l ?r`, and three goals are open: `?l`, `?r`, and the equation
`?h`. The built structure appears in `?h`'s target, so we focus that goal
with `case h` — the main goal right after the `refine` is `?l : DTree`,
which is just an opaque hole again.

Inside `case h`, both sides of the `⊢ =` tuple draw the `node` the
elaborator built, sharing the still-open holes `?l` and `?r` as atoms —
those hole atoms *are* the remaining goals. What the elaborator has figured
out draws as structure; what is still unknown draws as an atom. -/

example : ∃ t : DTree, t = t := by
  refine ⟨DTree.node ?l ?r, ?h⟩
  case h =>
    spytial.state
    rfl
  case l => exact .leaf 1
  case r => exact .leaf 2

/-! ## 3. A hypothesis knows structure (positive)

`h : t = DTree.node l r` refines `t`: its atom shows the `node` structure —
with `l` and `r` as opaque sub-holes — instead of an opaque leaf. The
hypothesis itself emits no extra edge; the refined structure is its
rendering. -/

set_option linter.unusedVariables false in
example (t l r : DTree) (h : t = DTree.node l r) : True := by
  spytial.state t
  trivial

-- the same refinement arises from a case split: `cases h : t` leaves the
-- branch's equation in its context. The two branches assume contradictory
-- things about `t` (`t = leaf v` in one, `t = node l r` in the other) —
-- exactly why one diagram is one goal: each `spytial.state` below draws its
-- own branch's refinement, never a merged picture
set_option linter.unusedVariables false in
example (t : DTree) : True := by
  cases h : t with
  | leaf v =>
    spytial.state
    trivial
  | node l r =>
    spytial.state
    trivial

/-! ## 4. A hypothesis rules structure out (negative)

`h2 : t ≠ DTree.node (leaf 0) (leaf 0)` emits into the `≠` relation — drawn
dashed red by default — against `t`'s *known* structure from `h`. What the
value looks like and what it does not, in one picture. -/

set_option linter.unusedVariables false in
example (t l r : DTree) (h : t = DTree.node l r)
    (h2 : t ≠ DTree.node (DTree.leaf 0) (DTree.leaf 0)) : True := by
  spytial.state t
  trivial

set_option linter.unusedVariables false in
example (t l r : DTree) (h : t = DTree.node l r)
    (h2 : t ≠ DTree.node (DTree.leaf 0) (DTree.leaf 0)) : True := by
  spytial.state.datum t
  trivial

/-! ## 5. Relational knowledge

`R` is a *local* relation (a variable, hence a free variable rather than a
constant), and `spytial.state` still names a relation after it: `h : R x y`
becomes the `R` tuple `x → y`, the goal the `⊢ R` tuple `y → x`, over the
same two atoms. `hsymm` is a `∀` — not a relation application — so it is
skipped, and the tactic logs a note saying so. -/

example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (hsymm : ∀ a b, R a b → R b a) : R y x := by
  spytial.state
  exact hsymm x y h

example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (hsymm : ∀ a b, R a b → R b a) : R y x := by
  spytial.state.datum
  exact hsymm x y h

/-! ## 6. Model finding: what CAN the hole be?

Everything above renders what is *known*. `spytial.find` searches: it
enumerates every `DTree` up to a constructor depth (default 3), keeps the
candidates on which all decidable hypotheses hold (`≠` is decidable here
because `DTree` derives `DecidableEq`), and draws the first survivor as `t`
— with the ruled-out value dashed red against the found model. Hypotheses
without a decision procedure are reported as unchecked, never assumed.
Zero survivors is an answer too: within the bound, no such value exists. -/

set_option linter.unusedVariables false in
example (t : DTree) (h : t ≠ DTree.leaf 0) : True := by
  spytial.find t
  trivial

-- the JSON view, at an explicit depth: the only depth-2 survivor of the two
-- disequalities is `node (leaf 0) (leaf 0)`
set_option linter.unusedVariables false in
example (t : DTree) (h : t ≠ DTree.leaf 0) (h2 : t ≠ DTree.leaf 1) : True := by
  spytial.find.datum t 2
  trivial

/-! ## Styling

There is no single subject type, so `spytial_spec` does not apply; ops go
through `with [...]`, checked against the live proof state. Decorated
relation names use escaped idents in field positions. -/

example (a b : Nat) (h : a < b) : a < b := by
  spytial.state with [edgeStyle «⊢ lt» (lineStyle "green")]
  exact h

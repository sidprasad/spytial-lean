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

`spytial.state` renders the current proof state — hypotheses and goals — so
both kinds are visible. Because tactics run during elaboration, `lake build
Demos` exercises everything below; the `.datum` variants print their JSON to
the build log, which is the headless verification mechanism. -/

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

After `refine ⟨DTree.node ?l ?r, ?h⟩` the witness metavariable is assigned
`DTree.node ?l ?r`. Instantiating reveals it: the goal `?h` mentions the
node with the two still-open holes `?l` and `?r` as atoms — those hole atoms
*are* the open goals. What the elaborator has figured out draws as
structure; what is still unknown draws as an atom. -/

example : ∃ t : DTree, t = t := by
  refine ⟨DTree.node ?l ?r, ?h⟩
  spytial.state
  case l => exact .leaf 1
  case r => exact .leaf 2
  case h => rfl

/-! ## 3. A hypothesis knows structure (positive)

`h : t = DTree.node l r` refines `t`: its atom shows the `node` structure —
with `l` and `r` as opaque sub-holes — instead of an opaque leaf. The
hypothesis itself emits no extra edge; the refined structure is its
rendering. -/

set_option linter.unusedVariables false in
example (t l r : DTree) (h : t = DTree.node l r) : True := by
  spytial.state t
  trivial

-- the same refinement arises inside a case split: `cases h : t` leaves the
-- branch equation in the context
set_option linter.unusedVariables false in
example (t : DTree) : True := by
  cases h : t with
  | leaf v => trivial
  | node l r =>
    spytial.state
    trivial

-- with BOTH branch goals open at once, the goals disagree about `t`. The
-- first branch's equation refines it; the second branch's stays an explicit
-- `=` edge against the drawn atom, so neither branch's knowledge is lost
set_option linter.unusedVariables false in
example (t : DTree) : True := by
  cases h : t
  spytial.state
  all_goals trivial

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

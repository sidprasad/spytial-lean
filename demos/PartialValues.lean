import SpytialLean

open SpytialLean

/-! # Diagramming partially-known values

In a proof you often hold a value you don't fully know — and mid-proof, the
local context knows things about it. The `spytial` tactic draws the value
using that knowledge. The subject is always the *value*; the context is the
knowledge source, never the thing drawn. There are two kinds of holes:

1. **Opaque hole** — all the context knows is the type. `t : DTree` with no
   facts draws as one atom of that type.
2. **Structured hole** — the context knows more. The knowledge comes from
   the elaborator (a `refine` or `let` partially built the term) or from the
   hypotheses (`h : t = node l r` says what `t` is; `h : t ≠ leaf 0` says
   what it is not; `h : R t u` is a fact anchored on it).

The goal is deliberately not drawn: hypotheses are established knowledge,
the goal is what is still being proven.

Tactics run during elaboration, so `lake build Demos` exercises everything
below; the `spytial.datum` variants print their JSON to the build log, which
is the headless verification mechanism. -/

inductive DTree where
  | leaf (value : Nat)
  | node (left right : DTree)
  deriving DecidableEq

/-! ## 1. An opaque hole

`t` is an abstract variable and nothing in the context mentions it: no
structure to descend into, so it renders as a single `DTree`-typed atom
labeled `t`. -/

set_option linter.unusedVariables false in
example (t : DTree) : True := by
  spytial t
  trivial

/-! ## 2. The elaborator knows structure

`let t := DTree.node ?l ?r` binds `t` to a partially built term. Drawing `t`
shows the `node` the elaborator has, with the still-open holes `?l` and `?r`
as atoms inside it — those hole atoms *are* the remaining goals, closed
below with `case`. What is already determined draws as structure; what is
still unknown draws as an atom. (The same applies to a metavariable assigned
by `refine`: assignments are instantiated before walking.) -/

example : True := by
  let t : DTree := DTree.node ?l ?r
  spytial t
  case l => exact .leaf 1
  case r => exact .leaf 2
  trivial

/-! ## 3. A hypothesis knows structure (positive)

`h : t = DTree.node l r` refines `t`: its atom shows the `node` structure —
with `l` and `r` as opaque sub-holes — instead of an opaque leaf. The
hypothesis itself emits no extra edge; the refined structure is its
rendering. -/

set_option linter.unusedVariables false in
example (t l r : DTree) (h : t = DTree.node l r) : True := by
  spytial t
  trivial

-- the same refinement arises from a case split: `cases h : t` leaves the
-- branch's equation in its context. The branches know contradictory things
-- about `t` (`t = leaf v` in one, `t = node l r` in the other), so the same
-- `spytial t` draws a different picture in each — the diagram always shows
-- what is known *here*
set_option linter.unusedVariables false in
example (t : DTree) : True := by
  cases h : t with
  | leaf v =>
    spytial t
    trivial
  | node l r =>
    spytial t
    trivial

/-! ## 4. A hypothesis rules structure out (negative)

A negative fact draws only between values already in the world — ruling a
term out is not license to materialize it. Here `u` is a real value whose
structure is known (`hu`), and `h : t ≠ u` draws one `≠` edge from `t` into
that structure: what `t` is not, without inventing atoms. The relation
*name* carries the semantics — `≠` is simply a different relation than `=`,
so nothing downstream can read "ruled out" as "holds" — and how it looks is
the spec author's choice (see the styling section below).

A negative fact against a term that is *not* in the world (`t ≠ leaf 0`) is
counted, not drawn — the tactic logs one note. -/

set_option linter.unusedVariables false in
example (t u : DTree) (hu : u = DTree.node (DTree.leaf 0) (DTree.leaf 0))
    (h : t ≠ u) : True := by
  spytial t
  trivial

set_option linter.unusedVariables false in
example (t u : DTree) (hu : u = DTree.node (DTree.leaf 0) (DTree.leaf 0))
    (h : t ≠ u) : True := by
  spytial.datum t
  trivial

/-! ## 5. Relational facts

Any Prop hypothesis mentioning the subject becomes a tuple anchored on its
atoms — here `R` is a *local* relation (a variable, hence a free variable
rather than a constant), and `h : R x y` still names the relation `R`.
`hsymm` never mentions `x`, so it is simply not this diagram's business; a
fact about `x` that does not decompose (the conjunction `hb`) is skipped,
and the tactic logs a note saying so. -/

set_option linter.unusedVariables false in
example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (hb : R x y ∧ R y x)
    (hsymm : ∀ a b, R a b → R b a) : R y x := by
  spytial x
  exact hsymm x y h

example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (hsymm : ∀ a b, R a b → R b a) : R y x := by
  spytial.datum x
  exact hsymm x y h

/-! ## Styling

The library never styles anything by default — that is the spec author's
job. The subject has a type, so a registered `spytial_spec` for it applies
unchanged; inline ops go through `with [...]`, elaborated against the
subject type's scope extended with the fact vocabulary. Negative relation
names use escaped idents in field positions — the ruled-out look, if you
want one, is one op: -/

set_option linter.unusedVariables false in
example (t u : DTree) (h : t ≠ u) : True := by
  spytial t with [edgeStyle «≠» (lineStyle "#cc0000" dashed)]
  trivial

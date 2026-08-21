import SpytialLean

open SpytialLean

/-! # Diagramming partially-known values

Mid-proof, you often hold a value you do not fully know. The context knows
things about it: equations, `let` bindings, facts. `spytial t` draws `t`
using that knowledge. The diagram always shows the *value*. The context is
only the source of knowledge — it is never drawn itself, and the goal is
never drawn either.

Each section below is one kind of knowledge. Tactics run at build time, so
`lake build Demos` checks all of it; the `spytial.datum` variants print
their JSON to the build log. -/

inductive DTree where
  | leaf (value : Nat)
  | node (left right : DTree)
  deriving DecidableEq

/-! ## 1. Nothing is known

We know nothing about `t` except its type.

**What you see:** one `DTree` atom named `t`. That is the whole diagram. -/

set_option linter.unusedVariables false in
example (t : DTree) : True := by
  spytial t
  trivial

/-! ## 2. Lean has already built part of the value

`let t := DTree.node ?l ?r` builds the top of `t` but leaves two holes.

**What you see:** the `node`, with two atoms `?l` and `?r` for the parts not
filled in yet. Those two atoms are exactly the two open goals — closed below
with `case`. Built parts draw as structure; unbuilt parts draw as atoms. -/

example : True := by
  let t : DTree := DTree.node ?l ?r
  spytial t
  case l => exact .leaf 1
  case r => exact .leaf 2
  trivial

/-! ## 3. A hypothesis says what the value IS

`h : t = DTree.node l r` tells us `t`'s shape.

**What you see:** `t` drawn as that `node`, with `l` and `r` as plain atoms
inside it. `h` itself adds no extra arrow — the shape *is* its picture. -/

set_option linter.unusedVariables false in
example (t l r : DTree) (h : t = DTree.node l r) : True := by
  spytial t
  trivial

/-! `cases h : t` gives each branch its own equation about `t`. So the same
`spytial t` draws a different picture in each branch: a `leaf` in the leaf
branch, a `node` in the node branch. The diagram always shows what is known
*here*. -/

set_option linter.unusedVariables false in
example (t : DTree) : True := by
  cases h : t with
  | leaf v =>
    spytial t
    trivial
  | node l r =>
    spytial t
    trivial

/-! ## 4. A hypothesis says what the value is NOT

`hu` says what `u` is. `h : t ≠ u` says `t` is not that.

**What you see:** the atom `t`, the known structure of `u`, and one arrow
from `t` to `u` in the relation named `≠`. The arrow's *name* carries the
meaning; nothing is styled unless you ask (see the last section).

One rule keeps this honest: a `≠` arrow only connects values that are
already in the diagram. `t ≠ DTree.leaf 0` names a tree that exists nowhere
in the context, so nothing is drawn for it — the tactic prints a note
counting it instead. Ruling a value out does not make it real. -/

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

/-! ## 5. A hypothesis relates the value to others

`h : R x y` is a fact linking `x` and `y`.

**What you see:** two atoms `x` and `y`, and one arrow from `x` to `y` in a
relation named `R`. Any fact that mentions the subject becomes an arrow like
this — that is how `y` gets into the picture at all. It works even though
`R` here is a local variable, not a global definition.

The other two hypotheses show the limits. `hb` mentions `x` but is an AND of
two facts, so it is not one arrow — it is not drawn, and the tactic prints a
note counting it. `hsymm` never mentions `x`, so it is simply ignored. -/

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

/-! ## 6. You pick the facts

`using [h, …]` replaces the automatic choice of facts with your own list.
Exactly the listed hypotheses are drawn, in that order — even ones that do
not mention the subject. Leave the list empty to draw no facts at all.

Refinements are not facts: `h : t = …` and `let` still shape the value
either way. They are what the value *is*, not an arrow hung on it.

**What you see below:** only the `h` arrow. `h2` is left out on purpose. -/

set_option linter.unusedVariables false in
example (a b : Nat) (h : a < b) (h2 : b < a) : True := by
  spytial a using [h]
  trivial

/-! ## Styling

Nothing is ever styled by default — how the diagram looks is the spec
author's job. A `spytial_spec` registered for the subject's type applies
as-is, and inline ops go through `with [...]`. The ruled-out look for `≠`,
if you want it, is one op (the `«…»` quotes are how Lean spells the unusual
name): -/

set_option linter.unusedVariables false in
example (t u : DTree) (h : t ≠ u) : True := by
  spytial t with [edgeStyle «≠» (lineStyle "#cc0000" dashed)]
  trivial

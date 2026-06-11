import SpytialLean

open SpytialLean

/-! # Proof-state visualization (`spytial_goals`)

The `spytial_goals` tactic renders the CURRENT proof state — every goal and its
local hypotheses — as one spatial relational diagram, instead of visualizing a
single named value the way `spytial`/`#spytial` do.

How the proof state maps to relations and atoms:

- A hypothesis whose **type is a Prop application** `R a b …` headed by a named
  symbol — either a constant (`LT.lt a b` from `a < b`) or a *local* relation
  introduced by a binder / `variable (R : …)` (which is a free variable, not a
  constant) — becomes a tuple in a relation named after `R`. The hypothesis
  binder name (e.g. `h`) is *not* rendered — the relation name carries the
  meaning. Only the data arguments are walked as atoms; proofs, types, and
  instance arguments (e.g. the `LT Nat` instance inside `a < b`) are dropped.
- A **data hypothesis** (a non-Prop type, e.g. `t : Tree`) is walked through the
  normal relationalizer into the same diagram. An *abstract* hypothesis variable
  (no definition) has no constructor structure, so it renders as a single atom
  typed by its type's head; a let-bound or concrete value decomposes.
- A Prop hypothesis that is **not** a named-symbol application (e.g. `∀ x, P x`,
  `A ∧ B`, `A → B`) is skipped, with a one-line `logInfo` note so it isn't
  silently missing.
- Each **goal** target gets the same Prop-application treatment, but its relation
  name is prefixed `⊢ ` so a spec can style goal structure differently from
  hypotheses. A goal that is not a decomposable Prop application becomes a single
  atom whose `type` field is `"Goal"`.

It is **experimental**: the output shape may change. Tactic diff, dependency
highlighting, and interactivity remain stretch goals (see issue #10).

Because tactics run during elaboration, `lake build Demos` exercises everything
below. The `spytial_goals_datum` calls print their JSON to the build log, which
is the verification mechanism — no infoview required.
-/

/-! ## The motivating example: a symmetric relation

`R` is a *local* relation (a `variable`, hence a free variable rather than a
constant), and `spytial_goals` still names a relation after it. `h : R x y`
becomes the relation `R` with the tuple `x → y`. The goal `R y x` becomes the
goal relation `⊢ R` with the tuple `y → x`. The hypothesis
`hsymm : ∀ a b, R a b → R b a` is a `∀`, not a relation application, so it is
skipped — and `spytial_goals` logs a note saying one hypothesis was skipped. -/

example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (hsymm : ∀ a b, R a b → R b a) : R y x := by
  spytial_goals
  exact hsymm x y h

-- The same proof state inspected as JSON (printed to the build log): two
-- relations — `R` with the tuple `x → y` (from `h`) and `⊢ R` with `y → x`
-- (from the goal). Four atoms: `α` and `R` (the data hypotheses, walked as
-- leaves), and `x`, `y` (shared between the `R` tuple and the `⊢ R` tuple, so
-- both edges point at the SAME two nodes). `hsymm` (a `∀`) is skipped, with the
-- one-line skip note.
example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (hsymm : ∀ a b, R a b → R b a) : R y x := by
  spytial_goals_datum
  exact hsymm x y h

/-! ## Mixed data + Prop hypotheses

The data hypothesis `t : Tree` is an abstract local variable (no definition), so
it has no constructor structure to descend into and renders as a single
`Tree`-typed atom labeled `t`. Alongside it, the Prop hypothesis `hlt : a < b`
is a const-headed application — `a < b` desugars to `@LT.lt Nat instLTNat a b`,
whose *data* args (after dropping the type, the `LT Nat` instance, and any
proofs) are `a` and `b` — so it becomes the relation `lt` with the tuple
`a → b`. Data atom and relational edge coexist in the *same* diagram. -/

inductive Tree where
  | leaf : Tree
  | node (key : Nat) (left : Tree) (right : Tree) : Tree
  deriving Repr

-- `t` and `hlt` are consumed by `spytial_goals` (it reads them out of the local
-- context), but the syntactic linter only sees uses in the *proof term*, where
-- they don't appear — hence we silence the unused-variable warning here.
set_option linter.unusedVariables false in
example (t : Tree) (a b : Nat) (hlt : a < b) : True := by
  spytial_goals
  trivial

-- JSON view of the mixed state: one `Tree`-typed atom for `t`, the `lt` relation
-- with the binary tuple `a → b` (the instance arg correctly dropped), and a
-- `Goal`-typed atom for the `True` goal (`True` is a nullary prop — no data args
-- to anchor a relation — so it falls back to a single `Goal` atom).
set_option linter.unusedVariables false in
example (t : Tree) (a b : Nat) (hlt : a < b) : True := by
  spytial_goals_datum
  trivial

/-! ## Multiple goals

`constructor` splits an `And` goal into two subgoals. With ≥ 2 goals open,
`spytial_goals` walks BOTH into one diagram: each `P`/`Q` goal target becomes its
own `⊢`-prefixed structure (here, single `Goal` atoms, since `P` and `Q` are
opaque propositions sharing no const head). -/

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  spytial_goals_datum
  · exact hp
  · exact hq

-- A multi-goal state where the goals ARE relation applications: after
-- `constructor` on `R x y ∧ R y x`, both subgoals decompose into `⊢ R` tuples
-- (`x → y` and `y → x`) in the shared diagram.
example {α : Type} (R : α → α → Prop) (x y : α)
    (hxy : R x y) (hyx : R y x) : R x y ∧ R y x := by
  constructor
  spytial_goals
  · exact hxy
  · exact hyx

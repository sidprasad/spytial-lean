import SpytialLean

open SpytialLean

/-! # Tactic-position smoke tests

Command coverage proves nothing about the tactics: `#spytial`* atoms tokenize
via the symbol path (`#` cannot begin an identifier), while the tactics are
subject to identifier lexing — see `spytialProofKw`. These tests elaborate
every tactic surface headlessly; a parse or elaboration failure fails the
build. -/

inductive TEven : Nat → Prop where
  | zero : TEven 0
  | add_two : TEven n → TEven (n + 2)

theorem teven_four : TEven 4 := .add_two (.add_two .zero)

-- data tactic on a global
example : True := by
  spytial [1, 2, 3]
  trivial

-- data tactic on a local hypothesis (widget payloads don't count as
-- references, so the unused-variable linter would fire spuriously)
set_option linter.unusedVariables false in
example (xs : List Nat) : True := by
  spytial xs
  trivial

-- data tactic with an inline spec
example : True := by
  spytial [1, 2, 3] with [hideAtom Nat]
  trivial

-- proof tactic on a global
example : True := by
  spytial.proof teven_four
  trivial

-- proof tactic on a local hypothesis
set_option linter.unusedVariables false in
example (h : TEven 4) : True := by
  spytial.proof h
  trivial

-- proof tactic with an inline spec
example : True := by
  spytial.proof teven_four with [hideAtom Nat]
  trivial

-- the tactics see hypotheses introduced by earlier tactics (withMainContext)
set_option linter.unusedVariables false in
example : ∀ n : Nat, True := by
  intro n
  spytial n
  trivial

set_option linter.unusedVariables false in
example : ∀ h : TEven 4, True := by
  intro h
  spytial.proof h
  trivial

-- proof-state tactic, bare
set_option linter.unusedVariables false in
example (a b : Nat) (h : a < b) : True := by
  spytial.state
  trivial

-- proof-state tactic after intro
set_option linter.unusedVariables false in
example : ∀ a b : Nat, a < b → True := by
  intro a b h
  spytial.state
  trivial

-- proof-state tactic with a subject
set_option linter.unusedVariables false in
example (xs ys : List Nat) (h : xs = ys) : True := by
  spytial.state xs
  trivial

-- proof-state tactic with ops: a hypothesis relation and an escaped goal
-- relation are both addressable in field positions
example (a b : Nat) (h : a < b) : a < b := by
  spytial.state with [edgeStyle lt (lineStyle "blue"),
                      edgeStyle «⊢ lt» (lineStyle "green")]
  exact h

-- proof-state datum tactic
set_option linter.unusedVariables false in
example (a b : Nat) (h : a < b) : True := by
  spytial.state.datum
  trivial

-- model finding: search, and search with an explicit depth
set_option linter.unusedVariables false in
example (xs : List Nat) (h : xs ≠ []) : True := by
  spytial.find xs
  trivial

set_option linter.unusedVariables false in
example (xs : List Nat) (h : xs ≠ []) : True := by
  spytial.find.datum xs 2
  trivial

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

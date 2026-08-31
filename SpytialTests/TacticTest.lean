import SpytialLean

open SpytialLean

/-! # Tactic-position smoke tests

Command coverage proves nothing about the tactics: `#spytial`* tokenizes via
the symbol path, the tactic keywords via identifier lexing. -/

inductive TEven : Nat → Prop where
  | zero : TEven 0
  | add_two : TEven n → TEven (n + 2)

theorem teven_four : TEven 4 := .add_two (.add_two .zero)

example : True := by
  spytial [1, 2, 3]
  trivial

-- widget payloads don't count as references, so the linter fires spuriously
set_option linter.unusedVariables false in
example (xs : List Nat) : True := by
  spytial xs
  trivial

example : True := by
  spytial [1, 2, 3] with [hideAtom Nat]
  trivial

example : True := by
  spytial.proof teven_four
  trivial

set_option linter.unusedVariables false in
example (h : TEven 4) : True := by
  spytial.proof h
  trivial

example : True := by
  spytial.proof teven_four with [hideAtom Nat]
  trivial

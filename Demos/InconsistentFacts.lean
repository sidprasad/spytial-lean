import SpytialLean

/-! # Inconsistent Facts — no diagram when no value fits

A diagram shows what is known about a value. If the known facts contradict each other,
no value satisfies them, so Spytial warns and draws nothing. -/

set_option linter.unusedVariables false

/-! ## Baseline -/

example (x : Nat) (hx : x = 3) : True := by
  spytial x
  trivial

/-! ## A false hypothesis

Warns: `spytial: inconsistent context; no diagram rendered`. -/

example (x : Nat) (hx : x = 3) (h : 1 = 2) : True := by
  spytial x
  trivial

/-! ## A false forward rule

`fyi` takes proofs, not statements: `fyi [1 = 2]` and `fyi [(sorry : 1 = 2)]` are errors.
A false rule is caught once what it derives (`x = 4`) clashes with what is known. -/

example (x : Nat) (hx : x = 3) (r : ∀ n, n = 3 → n = 4) : True := by
  spytial x fyi [r]
  trivial

/-! ## Leaving the contradiction out

`nvm` drops the false hypothesis, so the diagram renders again. -/

example (x : Nat) (hx : x = 3) (h : 1 = 2) : True := by
  spytial x nvm [h]
  trivial

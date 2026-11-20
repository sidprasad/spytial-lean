import SpytialLean

/-! # Inspecting a value with contradictory evidence

Select an inconsistent inspection to see which hypotheses Lean used to derive
`False` and what the same inspection produces with particular hypotheses omitted. -/

set_option linter.unusedVariables false

/-! ## Baseline -/

example (x : Nat) (hx : x = 3) : True := by
  spytial x
  trivial

/-! ## A false hypothesis

The conflict uses `h`. The preview omits it and shows `3` from `hx`. -/

example (x : Nat) (hx : x = 3) (h : 1 = 2) : True := by
  spytial x
  trivial

/-! ## A false forward rule

`fyi` takes proofs, not statements: `fyi [1 = 2]` and `fyi [(sorry : 1 = 2)]` are errors.
Here simplification detects a contradiction in `r` alone. Omitting `r` retains `hx`. -/

example (x : Nat) (hx : x = 3) (r : ∀ n, n = 3 → n = 4) : True := by
  spytial x fyi [r]
  trivial

/-! ## Overlapping and independent conflicts

Both `hn` and `other` contradict `hx`. The independent `bad` must also be
omitted. Compare keeping `hx` (the diagram shows `3`) with keeping the two
disequalities (the value of `x` is still symbolic). -/

example (x : Nat) (hx : x = 3) (hn other : x ≠ 3) (bad : False) : True := by
  spytial x
  trivial

/-! ## Leaving the contradiction out

`nvm` drops the false hypothesis, so the diagram renders again. -/

example (x : Nat) (hx : x = 3) (h : 1 = 2) : True := by
  spytial x nvm [h]
  trivial

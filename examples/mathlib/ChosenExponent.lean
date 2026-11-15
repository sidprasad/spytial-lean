import Mathlib.GroupTheory.OrderOfElement
import SpytialLean

/-!
# Which exponent did the inverse use?

In mathlib PR #6648, Jeremy Tan defined the inverse of `z` as `z ^ (n - 1)`.
The proof goal printed `Exists.choose …` where he expected `n`. He asked
how to tell whether this was the same exponent.

Below, `inversePower` is Tan's proposed inverse, using the current mathlib
lemma name. The first `change` exposes the exponent in his goal. Place the
cursor on `spytial n` to see what is known about that exponent. The exponent
in `x ^ n = 1` and the positive number in `0 < n` share one atom.

[Tan's question](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Getting.20values.20from.20an.20existential.20with.20a.20.22let.22.html#387031740)
· [mathlib PR #6648](https://github.com/leanprover-community/mathlib4/pull/6648)
-/

private noncomputable def inversePower {M : Type*} [Monoid M] {x : M}
    (hx : IsOfFinOrder x) (z : Submonoid.powers x) : Submonoid.powers x :=
  z ^ (hx.exists_pow_eq_one.choose - 1)

set_option linter.unusedTactic false in
example {M : Type*} [Monoid M] (x : M) (hx : IsOfFinOrder x) (z : Submonoid.powers x) :
    inversePower hx z * z = 1 := by
  obtain ⟨_, k, rfl⟩ := z
  apply Subtype.ext
  change (x ^ k) ^ (hx.exists_pow_eq_one.choose - 1) * x ^ k = 1
  -- Name the existential proof used in the goal. Keep just that evidence.
  generalize_proofs period
  clear hx
  let n := period.choose
  change (x ^ k) ^ (n - 1) * x ^ k = 1
  spytial n

  -- Use the two facts the inspector showed for this n.
  obtain ⟨hpos, hone⟩ : 0 < n ∧ x ^ n = 1 := period.choose_spec
  rw [← pow_succ, Nat.sub_add_cancel hpos, ← pow_mul, Nat.mul_comm, pow_mul, hone, one_pow]

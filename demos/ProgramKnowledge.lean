import SpytialLean

open SpytialLean

/-!
# Asking what Lean knows about a value

`#spytial` can draw an expression when the expression determines a complete
value. During a proof, however, the value you want to inspect is often a
variable. The expression alone says very little. Useful information is spread
across the local hypotheses: an equality may expose part of its structure, a
case split may establish an ordering, or an existential hypothesis may
guarantee an object whose identity is still unknown.

`spytial v` provides an interrogative interface: at any point in a proof, the
user can ask, "What does Lean know about `v` here?" IYKYK reads the current
hypotheses and returns facts about `v`. Spytial turns those facts into atoms
and relations. `spytial.datum v` prints the same data without drawing it.

The main example proves that insertion preserves sortedness. Place the cursor
on each `spytial` call to compare what Lean knows about `x` at that point in
the proof.
-/

/-- The insert step of insertion sort. -/
def orderedInsert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: orderedInsert x ys

inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | single (a : Nat) : Sorted [a]
  | cons (a b : Nat) (l : List Nat) (hab : a ≤ b) (rest : Sorted (b :: l)) :
      Sorted (a :: b :: l)

/-! ## A complete value

This expression contains all the information needed to compute and draw the
result. No proof context is needed. -/

#spytial (orderedInsert 4 [1, 3, 5])

/-! ## A value constrained by hypotheses

In the theorem below, `x` remains a variable. Inspecting `x` by itself would
show only one atom. As the proof proceeds, the local hypotheses establish how
`x` is ordered relative to the elements of the list. `spytial x` displays
those established relations even though Lean never computes a concrete value
for `x`. -/

theorem sorted_orderedInsert (x : Nat) {l : List Nat} (h : Sorted l) :
    Sorted (orderedInsert x l) := by
  spytial x
  induction h with
  | nil => exact .single x
  | single b =>
    -- Lean knows `x` and `b`, but it does not yet know how they are ordered.
    -- The diagram therefore contains only `x`.
    spytial x
    by_cases hxb : x ≤ b
    · -- In this branch, `hxb` proves `x ≤ b`. The diagram now shows that relation.
      spytial x
      simp only [orderedInsert, if_pos hxb]
      exact .cons x b [] hxb (.single b)
    · have hbx : b ≤ x := by omega
      simp only [orderedInsert, if_neg hxb]
      exact .cons b x [] hbx (.single x)
  | cons a b l hab rest ih =>
    by_cases hxa : x ≤ a
    · -- This branch does not use the recursive insertion described by `ih`.
      -- Removing it keeps the example focused on facts about this branch.
      clear ih
      -- The context proves `x ≤ a` and `a ≤ b`.
      spytial x
      simp only [orderedInsert, if_pos hxa]
      exact .cons x a _ hxa (.cons a b l hab rest)
    · have hax : a ≤ x := by omega
      simp only [orderedInsert, if_neg hxa]
      simp only [orderedInsert] at ih ⊢
      by_cases hxb : x ≤ b
      · clear ih
        rw [if_pos hxb]
        -- The context now proves `a ≤ x` and `x ≤ b`. The diagram shows `x`
        -- at its insertion point between two adjacent list elements.
        spytial x with [orientation le right]
        spytial.datum x
        exact .cons a x _ hax (.cons x b l hxb rest)
      · rw [if_neg hxb] at ih ⊢
        -- Lean has not determined where `x` occurs in the tail. It does know,
        -- through `ih`, that the result of the recursive insertion is sorted.
        spytial x
        exact .cons a b _ hab ih

/-! ## Supplying a useful hypothesis

The `fyi` clause supplies an additional proved hypothesis to IYKYK. Here,
`Nat.le_trans` derives `x ≤ b` from `x ≤ a` and `a ≤ b`. The derived relation
appears even though no local hypothesis states it directly. -/

set_option linter.unusedVariables false in
example (x a b : Nat) (hxa : x ≤ a) (hab : a ≤ b) : True := by
  spytial x fyi [Nat.le_trans]
  trivial

/-! ## An object whose identity is unknown

The hypothesis `h` guarantees that `l` has a head and that `x` is less than or
equal to that head. Before `obtain`, the head has no name in the proof. IYKYK
preserves its existential binder as `yˀ`, and Spytial uses that same atom in
the list and in the ordering relation. After `obtain`, `y` becomes a local name
and the equality gives `l` its known list structure. -/

set_option linter.unusedVariables false in
example (x : Nat) (l : List Nat) (h : ∃ y t, l = y :: t ∧ x ≤ y) : True := by
  spytial l
  obtain ⟨y, t, hl, hxy⟩ := h
  spytial l
  trivial

/-! ## A disjunction does not choose a branch

The hypothesis below proves `x ≤ b ∨ b ≤ x`, but it does not prove either
comparison separately. Spytial therefore shows neither relation. A later case
split could make one of them available. -/

set_option linter.unusedVariables false in
example (x b : Nat) (choice : x ≤ b ∨ b ≤ x) : True := by
  spytial x
  trivial

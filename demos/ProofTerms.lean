import SpytialLean

open SpytialLean

/-! # Proof Term Visualization

In Lean, proofs are terms. Spytial visualizes terms.
Therefore: Spytial can visualize proof structures.

This demo explores what proof terms look like when visualized.
-/

/-! ## Reflexive Transitive Closure (Star)

A classic inductive predicate. A proof of `Star r a c` is a
chain of steps: a → b → ... → c. Can we see the chain? -/

inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl : Star r a a
  | step : r a b → Star r b c → Star r a c

-- A simple "successor" relation on Nat
inductive Step : Nat → Nat → Prop where
  | mk : Step n (n + 1)

-- Proof that 0 can reach 3 via Step
def zeroToThree : Star Step 0 3 :=
  .step .mk (.step .mk (.step .mk .refl))

-- Can we see the chain 0 → 1 → 2 → 3?
#spytial.proof zeroToThree
#spytial.proof.datum zeroToThree

/-! ## Even predicate

Another classic — proof that a number is even is either
`zero` or `add_two` applied to a smaller proof. -/

inductive MyEven : Nat → Prop where
  | zero : MyEven 0
  | add_two : MyEven n → MyEven (n + 2)

def even_six : MyEven 6 :=
  .add_two (.add_two (.add_two .zero))

-- Should show a chain: add_two → add_two → add_two → zero
#spytial.proof even_six
#spytial.proof.datum even_six

/-! ## List membership proof

A proof that an element is in a list has structure too. -/

def three_in_list : 3 ∈ [1, 2, 3, 4, 5] := by decide

#spytial.proof three_in_list

/-! ## Simple logical proof terms -/

-- An And.intro has two sub-proofs
def and_proof : True ∧ True := ⟨trivial, trivial⟩
#spytial.proof and_proof
#spytial.proof.datum and_proof

-- An Or.inl / Or.inr shows which branch was taken
def or_proof : True ∨ False := Or.inl trivial
#spytial.proof or_proof
#spytial.proof.datum or_proof

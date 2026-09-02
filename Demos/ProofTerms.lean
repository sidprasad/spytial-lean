import SpytialLean

open SpytialLean

/-! # Proof Term Visualization -/

inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl : Star r a a
  | step : r a b → Star r b c → Star r a c

inductive Step : Nat → Nat → Prop where
  | mk : Step n (n + 1)

def zeroToThree : Star Step 0 3 :=
  .step .mk (.step .mk (.step .mk .refl))

#spytial.proof zeroToThree
#spytial.proof.datum zeroToThree

inductive MyEven : Nat → Prop where
  | zero : MyEven 0
  | add_two : MyEven n → MyEven (n + 2)

def even_six : MyEven 6 :=
  .add_two (.add_two (.add_two .zero))

#spytial.proof even_six
#spytial.proof.datum even_six

def three_in_list : 3 ∈ [1, 2, 3, 4, 5] := by decide

#spytial.proof three_in_list

def and_proof : True ∧ True := ⟨trivial, trivial⟩
#spytial.proof and_proof
#spytial.proof.datum and_proof

def or_proof : True ∨ False := Or.inl trivial
#spytial.proof or_proof
#spytial.proof.datum or_proof

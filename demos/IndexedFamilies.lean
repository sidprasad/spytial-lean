import SpytialLean

open SpytialLean

/-! # Indexed inductive families

For an indexed inductive family the *index* carries information that the
constructor name alone does not. A length-indexed `Vec` is the canonical case:
`Vec.nil : Vec α 0` and a `Vec.cons … : Vec α 2` are different shapes, but their
constructor atoms would be labeled just `nil` and `cons` — indistinguishable at
a glance.

When a constructor's inductive has `numIndices > 0`, the relationalizer reads
the trailing index expressions off the value's *type* and appends them to the
atom label, e.g. `cons : Vec 2`, `nil : Vec 0`. Only the label changes — the
atom `type` field stays the head constant short name (`Vec`), so selectors that
match on `type` are unaffected.
-/

/-! ## A length-indexed vector

`Vec α n` is indexed by its length `n : Nat` (one index, `numIndices = 1`).
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (head : α) (tail : Vec α n) : Vec α (n + 1)

/-- A 2-element vector, so its root has type `Vec Nat 2`. -/
def v : Vec Nat 2 := .cons 10 (.cons 20 .nil)

-- Labels carry the length: the root reads `cons : Vec 2`, the next `cons : Vec 1`,
-- and the terminal `nil : Vec 0`. The `type` field stays `Vec` throughout.
#spytial v

#spytial.datum v

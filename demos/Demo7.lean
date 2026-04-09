import SpytialLean

open SpytialLean

/-! # Demo 7 — Type class instance visualization (Issue #7)

Exploring how type class instances render with `#spytial`.
Type classes are structures under the hood — do they decompose?
-/

/-! ## Simple custom type class -/

class HasIdentity (α : Type) where
  identity : α

instance : HasIdentity Nat where
  identity := 0

instance : HasIdentity String where
  identity := ""

-- Can we visualize a synthesized instance?
#spytial (inferInstance : HasIdentity Nat)
#spytial.datum (inferInstance : HasIdentity Nat)

#spytial (inferInstance : HasIdentity String)
#spytial.datum (inferInstance : HasIdentity String)

/-! ## Class with multiple fields -/

class MyAlgebra (α : Type) where
  zero : α
  one : α
  add : α → α → α

instance : MyAlgebra Nat where
  zero := 0
  one := 1
  add := Nat.add

-- Multiple data fields — do they all appear?
-- `add` is function-valued — does it get expanded (from #6 fix)?
#spytial (inferInstance : MyAlgebra Nat)
#spytial.datum (inferInstance : MyAlgebra Nat)

/-! ## Class with proof fields -/

class MyMonoid (α : Type) extends MyAlgebra α where
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a

instance : MyMonoid Nat where
  zero := 0
  one := 1
  add := Nat.add
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add

-- Proof fields (add_zero, zero_add) should be filtered by #5 fix.
-- Data fields (zero, one, add) should appear.
#spytial (inferInstance : MyMonoid Nat)
#spytial.datum (inferInstance : MyMonoid Nat)

/-! ## Lean's built-in classes -/

-- Does Lean's own Add instance decompose?
#spytial (inferInstance : Add Nat)
#spytial.datum (inferInstance : Add Nat)

/-! ## Direct instance value (not via inferInstance) -/

def myInst : HasIdentity Nat := { identity := 42 }
#spytial myInst
#spytial.datum myInst

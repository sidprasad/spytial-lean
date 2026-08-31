import SpytialLean

open SpytialLean

/-! # Type Class Instances -/

class HasIdentity (α : Type) where
  identity : α

instance : HasIdentity Nat where
  identity := 0

instance : HasIdentity String where
  identity := ""

#spytial (inferInstance : HasIdentity Nat)
#spytial.datum (inferInstance : HasIdentity Nat)

#spytial (inferInstance : HasIdentity String)
#spytial.datum (inferInstance : HasIdentity String)

class MyAlgebra (α : Type) where
  zero : α
  one : α
  add : α → α → α

instance : MyAlgebra Nat where
  zero := 0
  one := 1
  add := Nat.add

#spytial (inferInstance : MyAlgebra Nat)
#spytial.datum (inferInstance : MyAlgebra Nat)

class MyMonoid (α : Type) extends MyAlgebra α where
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a

instance : MyMonoid Nat where
  zero := 0
  one := 1
  add := Nat.add
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add

#spytial (inferInstance : MyMonoid Nat)
#spytial.datum (inferInstance : MyMonoid Nat)

#spytial (inferInstance : Add Nat)
#spytial.datum (inferInstance : Add Nat)

def myInst : HasIdentity Nat := { identity := 42 }
#spytial myInst
#spytial.datum myInst

import SpytialLean

open SpytialLean

/-! # Proof Field Filtering

Proof fields are filtered out by `isProofArg`; only data fields are drawn. -/

structure MySubgroup (G : Type) where
  carrier : List G
  identity : G
  mul_closed : ∀ a b, a ∈ carrier → b ∈ carrier → True
  id_mem : identity ∈ carrier

def exampleSubgroup : MySubgroup Nat :=
  { carrier := [0, 1, 2]
    identity := 0
    mul_closed := fun _ _ _ _ => trivial
    id_mem := List.Mem.head _ }

#spytial exampleSubgroup

structure BoundedNat where
  val : Nat
  bound : Nat
  inBounds : val < bound

def myBounded : BoundedNat :=
  { val := 3, bound := 10, inBounds := by omega }

#spytial myBounded

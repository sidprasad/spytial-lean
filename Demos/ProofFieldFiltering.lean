import SpytialLean

open SpytialLean

/-! # Proof Field Filtering

Structures carrying proof obligations (common in algebra) should only
visualize their *data* fields. Proof fields are filtered by `isProofArg`.
-/

/-! ## Subgroup-like structure with proof fields -/

structure MySubgroup (G : Type) where
  carrier : List G
  identity : G
  mul_closed : ∀ a b, a ∈ carrier → b ∈ carrier → True  -- proof field
  id_mem : identity ∈ carrier                             -- proof field

def exampleSubgroup : MySubgroup Nat :=
  { carrier := [0, 1, 2]
    identity := 0
    mul_closed := fun _ _ _ _ => trivial
    id_mem := List.Mem.head _ }

-- Only `carrier` and `identity` should appear as nodes.
-- `mul_closed` and `id_mem` are Prop-typed and should be filtered out.
#spytial exampleSubgroup

/-! ## Bounded value — data + proof mix -/

structure BoundedNat where
  val : Nat
  bound : Nat
  inBounds : val < bound  -- proof field

def myBounded : BoundedNat :=
  { val := 3, bound := 10, inBounds := by omega }

-- Only `val` and `bound` should appear; `inBounds` should be filtered.
#spytial myBounded

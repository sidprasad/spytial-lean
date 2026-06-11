import SpytialLean

open SpytialLean

/-! # Quotient types

`Quot` is kernel-primitive: `Quot.mk` is registered as `.quotInfo`, not as a
constructor (`.ctorInfo`), so the relationalizer's constructor dispatch misses
it and a quotient value would otherwise render as an opaque leaf.

The relationalizer special-cases applications headed by `Quot.mk` (and the
`Quotient.mk` / `Quotient.mk'` const heads, which usually reduce to `Quot.mk`
under whnf). Such a value becomes an atom labeled `⟦·⟧` — the equivalence-class
brackets — whose representative is walked as a child connected by a relation
named `repr`. The atom's `type` is the head name of the value's type (`Quot`,
`Quotient`, or a user def if whnf keeps it).

The diagram therefore reads: "this is an equivalence class `⟦·⟧`, and here
(`repr`) is the underlying representative we chose."
-/

/-! ## `Quot.mk` with an explicit relation

No `Setoid` instance or equivalence proof is needed for `Quot.mk` — it takes the
relation and the representative directly. Here the relation is "same value mod
3", and `5` is the representative.
-/

#spytial (Quot.mk (fun a b : Nat => a % 3 = b % 3) 5)

-- The `repr` edge points at the `Nat` atom `5`.
#spytial.datum (Quot.mk (fun a b : Nat => a % 3 = b % 3) 5)

/-! ## `Quotient.mk` via a `Setoid`

A `Setoid` on `Nat × Nat` whose relation `r a b := a.1 + b.2 = b.1 + a.2`
identifies pairs with the same difference (the usual integer construction). The
`iseqv` proof is short with `omega`.
-/

instance diffSetoid : Setoid (Nat × Nat) where
  r a b := a.1 + b.2 = b.1 + a.2
  iseqv := {
    refl := fun a => by omega
    symm := fun h => by omega
    trans := fun h1 h2 => by omega
  }

-- `(3, 1)` represents the class of pairs with difference 2.
#spytial (Quotient.mk diffSetoid (3, 1))

-- The `repr` edge points at the `Prod` representative `(3, 1)`.
#spytial.datum (Quotient.mk diffSetoid (3, 1))

import SpytialLean

open SpytialLean

/-! # Spec inheritance through structure parent chains (issue #2)

A `spytial_spec` attached to a type is the default layout used when a value of
that type is visualized. This demo verifies — empirically, in the build log —
that the spec lookup walks the *structure parent chain*, so a value of a derived
type inherits the spec attached to its base type.

The mechanism under test is `lookupTypeSpec` in `SpytialLean/Command.lean`. For a
value whose head type is a structure, it reads the parent structures
(`getAllParentStructures`, C3 linearization) and composes their specs root-first,
merging the YAML (`mergeSpecYamls`). Because Lean 4 *classes are structures*, the
exact same path makes `class B extends A` inherit `A`'s spec — no extra code.

The `#spytial.typespec <term>` debug command prints precisely the YAML that
`lookupTypeSpec` resolves (or `none`). It is the cleanest assertion of inheritance:
if the parent chain works, the printed YAML contains lines from *every* spec in the
chain. Each spec below uses a recognizable `.atomColor` value so you can read off,
from the merged YAML, which specs were composed.

Run `lake build Demos` and read the `#spytial.typespec` info diagnostics in the
build log to see the merged YAML for each case.
-/

/-! ## 1. Baseline: plain structure extension

`Derived extends Base`. A spec on `Base` should apply to a `Derived` value, and a
spec on `Derived` itself should compose with it (root-first: Base, then Derived).
-/

structure Base where
  tag : Nat
  deriving Repr

structure Derived extends Base where
  extra : Nat
  deriving Repr

-- Distinct, recognizable colors so the merged YAML is self-documenting.
spytial_spec Base [
  .atomColor (selector := "Base") (value := "#336699")
]

spytial_spec Derived [
  .atomColor (selector := "Derived") (value := "#cc3300")
]

def aDerived : Derived := { tag := 1, extra := 2 }

-- The diagram uses the inherited+own spec as its default.
#spytial aDerived

-- Spec lookup, asserted in the build log. Expect the MERGED YAML containing both
-- the Base color (#336699) and the Derived color (#cc3300), Base-first.
#spytial.typespec aDerived

-- A bare `Base` value resolves only Base's spec.
def aBase : Base := { tag := 0 }
#spytial.typespec aBase

/-! ## 2. Type classes: `class Dog extends Animal`

Lean 4 classes are structures, so this exercises the very same parent-chain path.
A spec on the parent class `Animal` must apply to a `Dog` instance value.
-/

class Animal (α : Type) where
  legs : Nat

class Dog (α : Type) extends Animal α where
  goodBoy : Bool

instance : Animal Unit where
  legs := 4

instance : Dog Unit where
  legs := 4
  goodBoy := true

spytial_spec Animal [
  .atomColor (selector := "Animal") (value := "#118811")
]

spytial_spec Dog [
  .atomColor (selector := "Dog") (value := "#8811cc")
]

-- A `Dog` instance value. `inferInstance` synthesizes the registered instance.
def aDog : Dog Unit := inferInstance

#spytial aDog

-- Expect the MERGED YAML: Animal color (#118811) then Dog color (#8811cc).
-- This is the key result: a parent *class*'s spec reaches a child instance.
#spytial.typespec aDog

-- An `Animal` instance resolves only Animal's spec.
def anAnimal : Animal Unit := inferInstance
#spytial.typespec anAnimal

/-! ## 3. Deeper chain (3 levels): C3 linearization order

`Vehicle ← Car ← SportsCar`. The composed YAML must list the specs root-first
(Vehicle, Car, SportsCar), demonstrating the C3 linearization order produced by
`getAllParentStructures` (reversed to root-first, self last).
-/

structure Vehicle where
  wheels : Nat
  deriving Repr

structure Car extends Vehicle where
  doors : Nat
  deriving Repr

structure SportsCar extends Car where
  topSpeed : Nat
  deriving Repr

spytial_spec Vehicle [
  .atomColor (selector := "Vehicle") (value := "#111111")
]

spytial_spec Car [
  .atomColor (selector := "Car") (value := "#222222")
]

spytial_spec SportsCar [
  .atomColor (selector := "SportsCar") (value := "#333333")
]

def aSportsCar : SportsCar := { wheels := 4, doors := 2, topSpeed := 300 }

#spytial aSportsCar

-- Expect the MERGED YAML in root-first order:
--   Vehicle (#111111), Car (#222222), SportsCar (#333333).
#spytial.typespec aSportsCar

/-! ## Deferred cases (issue #2 stays open)

The issue also asks for three further forms of spec inheritance. All three are
deferred with rationale recorded in `PLAN.md` (the "#2" section); see
<https://github.com/sidprasad/spytial-lean/issues/2>. They are NOT implemented
here:

1. **Explicit `spytial_spec X extends Y` syntax** for plain inductives that are
   *not* connected by a structure parent chain (e.g. an `RBNode` that should
   reuse a `Tree` spec). New surface syntax for a niche need — wait for demand.

2. **Per-instantiation specs** (`List Nat` distinct from `List`). The spec store
   is keyed by `Name`, so it cannot today distinguish a type by its arguments.
   Keying by type *expression* is a storage-format migration — follow-up.

3. **Subtype inheritance.** A value of `{x : Nat // x > 0}` is headed by
   `Subtype` and is a `Subtype.mk` pair; silently inheriting `Nat`'s spec would
   mislabel the wrapper atom. Needs its own design.

### Status quo for the Subtype case

The current behavior, as documentation: a Subtype value resolves NO spec, because
its head type is `Subtype` (no `spytial_spec` attached) and `lookupTypeSpec` does
not unwrap it. Expect `#spytial.typespec` to print `none` below even though `Nat`
itself could carry a spec — confirming that Subtype inheritance is not (yet) wired.
-/

def aPositive : { x : Nat // x > 0 } := ⟨1, by decide⟩

-- Expect: none (Subtype carries no spec; the base type's spec is not inherited).
#spytial.typespec aPositive

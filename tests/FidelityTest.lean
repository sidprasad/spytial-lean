module

public import SpytialLean.Identity
public meta import SpytialLean

open SpytialLean Lean Elab

/-! # Fidelity: the datum reproduces the host's inspection string

The commitment under test, for Lean's corner of the multilanguage work:
for literal values and values of inductive types (including structures),
compare the two paths

    v ─ reprStr ────────────────────────────→ string
    v ─ relationalize ─ reifyDatum ─ reprStr → string

`#spytial.fidelity` runs both and prints the shared string; each `#guard_msgs`
below pins the printed form, so a test asserts *both* that the paths agree and
what they agree on. The reconstructor sees only the `JsonDataInstance`.

Each passing case is also a kernel-certified theorem instance: `checkFidelity`
requires the kernel to accept `rfl : v = reified v`, with the datum-only
syntax placed at the original type (the datum records no type parameters, so
the equality's *statement* needs the type; the reconstruction never saw it).
The universal, conditional version of that statement — lossless for every
value whenever identity merges only equal skeletons and field names are
distinct — is the `fidelity` theorem in `SpytialLean.Fidelity`; these are its
per-value, unconditional instances on the real walker's output. -/

/-! ## Literals -/

/-- info: 42 -/
#guard_msgs in #spytial.fidelity (42 : Nat)

/-- info: 0 -/
#guard_msgs in #spytial.fidelity (0 : Nat)

/-- info: "hello" -/
#guard_msgs in #spytial.fidelity "hello"

/-- info: "" -/
#guard_msgs in #spytial.fidelity ""

-- the datum's label holds the contents unescaped; reconstruction recovers
-- them exactly, and both paths print the escaped form
/-- info: "a\"b" -/
#guard_msgs in #spytial.fidelity "a\"b"

/-- info: 'a' -/
#guard_msgs in #spytial.fidelity 'a'

/-! ## Inductive types -/

/-- info: true -/
#guard_msgs in #spytial.fidelity true

-- Int values walk as `ofNat`/`negSucc` constructor atoms
/-- info: -5 -/
#guard_msgs in #spytial.fidelity (-5 : Int)

/-- info: 5 -/
#guard_msgs in #spytial.fidelity (5 : Int)

-- the datum spells this `Nat|zero`, not a literal; both paths print `0`
/-- info: 0 -/
#guard_msgs in #spytial.fidelity Nat.zero

/-- info: [1, 2, 3] -/
#guard_msgs in #spytial.fidelity [1, 2, 3]

-- a parameter no value pins down never reaches the printout; `reifyDatum`
-- defaults it
/-- info: [] -/
#guard_msgs in #spytial.fidelity ([] : List Nat)

/-- info: [[1], [2, 3]] -/
#guard_msgs in #spytial.fidelity [[1], [2, 3]]

/-- info: some 5 -/
#guard_msgs in #spytial.fidelity (some 5)

/-- info: none -/
#guard_msgs in #spytial.fidelity (none : Option Nat)

/-- info: Sum.inl 3 -/
#guard_msgs in #spytial.fidelity (Sum.inl 3 : Nat ⊕ String)

public inductive FTree where
  | leaf (n : Nat)
  | branch (left right : FTree)
  deriving Repr

/-- info: FTree.branch (FTree.leaf 1) (FTree.branch (FTree.leaf 2) (FTree.leaf 3)) -/
#guard_msgs in #spytial.fidelity (FTree.branch (.leaf 1) (.branch (.leaf 2) (.leaf 3)))

public inductive Color where
  | red | green | blue
  deriving Repr

/-- info: Color.green -/
#guard_msgs in #spytial.fidelity Color.green

namespace FNS
public inductive Wrapped where
  | box (n : Nat)
  deriving Repr
end FNS

-- the datum records only the short head name `Wrapped`; outside `FNS` that
-- resolves through the environment fallback, not the command-site scope
/-- info: FNS.Wrapped.box 7 -/
#guard_msgs in #spytial.fidelity (FNS.Wrapped.box 7)

/-! ## Structures -/

public structure FPoint where
  x : Nat
  y : Nat
  deriving Repr

/-- info: { x := 1, y := 2 } -/
#guard_msgs in #spytial.fidelity ({ x := 1, y := 2 } : FPoint)

public structure FLine where
  p : FPoint
  q : FPoint
  deriving Repr

/-- info: { p := { x := 0, y := 0 }, q := { x := 3, y := 4 } } -/
#guard_msgs in #spytial.fidelity ({ p := ⟨0, 0⟩, q := ⟨3, 4⟩ } : FLine)

public structure FBox (α : Type) where
  val : α
  deriving Repr

/-- info: { val := "in" } -/
#guard_msgs in #spytial.fidelity ({ val := "in" } : FBox String)

/-- info: (1, "a") -/
#guard_msgs in #spytial.fidelity (1, "a")

/-! ## The datum may contain more than the printout

Structural identity merges the two equal leaves into one atom; the printout
duplicates them. Reconstruction unfolds the sharing, so the strings agree. -/

public inductive STree where
  | leaf (n : Nat)
  | branch (left right : STree)
  deriving Repr, SpytialIdentity

/-- info: STree.branch (STree.leaf 1) (STree.leaf 1) -/
#guard_msgs in #spytial.fidelity (STree.branch (.leaf 1) (.leaf 1))

/-! ## Boundaries

Reconstruction failing is itself pinned, so a fix that moves a boundary shows
up here. -/

/-- Assert that reconstruction from the datum alone fails for this value. -/
meta def assertNoReify (t : Term) : TermElabM Unit := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let di ← relationalize (← instantiateMVars e)
  let ok ← try discard (reifyDatum di); pure true catch _ => pure false
  if ok then throwError "expected reification to fail"

-- the atom records only the type head, so `Fin 5`'s index is not in the
-- datum: nothing determines what `val` must be less than
#eval show TermElabM Unit from do assertNoReify (← `((3 : Fin 5)))

public inductive DupBinder where
  | mk (x : Nat) (x : Nat)
  deriving Repr

-- two fields sharing a binder name collapse into one relation
-- (`fieldRelName` keeps user-written names); reconstruction detects the
-- collision rather than guessing an order
#eval show TermElabM Unit from do assertNoReify (← `(DupBinder.mk 1 2))

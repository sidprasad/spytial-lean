module

public meta import SpytialLean

open SpytialLean

namespace CoverageFixture

public structure Graph where
  nodes : Nat
  edges : Nat

public inductive Rope where
  | leaf (s : String)
  | cat (l r : Rope)

public inductive Waived where
  | a | b

public inductive Gap where
  | mk (n : Nat)

public inductive IsEven : Nat → Prop where
  | zero : IsEven 0
  | step (n : Nat) : IsEven n → IsEven (n + 2)

public class Widget (α : Type) where
  render : α → String

end CoverageFixture

-- deliberately non-public: registration must resolve the private-mangled name
meta def ropeRel : CustomRelationalizer := fun _ _ => do
  modify fun s : WalkState => s.addAtom { id := "rope", type := "Rope", label := "rope" }
  return "rope"

-- deliberately relative names: registration must resolve them to the FQNs
-- the enumeration produces
namespace CoverageFixture

spytial_spec Graph [hideAtom Nat]
-- `ropeRel` is deliberately non-`public`, pinning the registration warning.
/--
warning: '_private.SpytialTests.CoverageTest.0.ropeRel' is not `public`, so a `#spytial` on this type from an importing module fails at render with `Unknown constant` — declare it `public meta def`
-/
#guard_msgs in
spytial_relationalizer Rope ropeRel
spytial_opt_out Waived "structural noise, not domain data"

end CoverageFixture

/--
warning: Spytial coverage for 'CoverageFixture': 3/4 covered, 1 uncovered:
  • CoverageFixture.Gap
Attach a spec with `spytial_spec <Name> [...]`, register a custom relationalizer with `spytial_relationalizer`, or waive with `spytial_opt_out <Name> "reason"`.
-/
#guard_msgs in
#spytial.coverage CoverageFixture

/--
error: Spytial coverage for 'CoverageFixture': 3/4 covered, 1 uncovered:
  • CoverageFixture.Gap
Attach a spec with `spytial_spec <Name> [...]`, register a custom relationalizer with `spytial_relationalizer`, or waive with `spytial_opt_out <Name> "reason"`.
-/
#guard_msgs in
#spytial.coverage! CoverageFixture

spytial_opt_out CoverageFixture.Gap "leaf placeholder, revisit"

/--
info: Spytial coverage: 4/4 data types in 'CoverageFixture' covered.
-/
#guard_msgs in
#spytial.coverage CoverageFixture

/--
error: Unknown constant `CoverageFixture.DoesNotExist`
-/
#guard_msgs in
spytial_opt_out CoverageFixture.DoesNotExist "x"

/-! ## Strict gate + empty-namespace guard -/

-- Strict `!` on a fully-covered namespace succeeds — pinning the clean pass so
-- the empty-root guard below cannot regress it into a false failure.
/--
info: Spytial coverage: 4/4 data types in 'CoverageFixture' covered.
-/
#guard_msgs in
#spytial.coverage! CoverageFixture

-- A namespace matching nothing fails strict mode instead of reporting a hollow
-- 0/0 pass …
/--
error: no Spytial coverage data types found under 'NoSuchNamespace' — check the spelling and that the namespace is imported
-/
#guard_msgs in
#spytial.coverage! NoSuchNamespace

-- … and warns (never the success line) in the plain form.
/--
warning: no Spytial coverage data types found under 'NoSuchNamespace' — check the spelling and that the namespace is imported
-/
#guard_msgs in
#spytial.coverage NoSuchNamespace

/-! ## Inherited spec counts as covered -/

namespace CovInherit

public structure Parent where
  a : Nat

public structure Child extends Parent where
  b : Nat

spytial_spec Parent [hideAtom Nat]

end CovInherit

-- Child has no own spec but renders via Parent's inherited spec — strict passes.
/--
info: Spytial coverage: 2/2 data types in 'CovInherit' covered.
-/
#guard_msgs in
#spytial.coverage! CovInherit

/-! ## Custom-relationalizer referential integrity

A value whose type has a custom relationalizer, appearing twice, must not leave a
tuple pointing at the pre-allocated id the relationalizer discards. `boxedRel`
returns its own fresh id (like the demo's SimpleGraph), and the second occurrence
of `boxedTwice`'s components hits the seen-cache. -/

public structure Boxed where
  n : Nat

public meta def boxedRel : CustomRelationalizer := fun _ _ => do
  let s ← get
  let (bid, s) := s.freshId
  set s
  modify (·.addAtom { id := bid, type := "Boxed", label := "boxed" })
  return bid

spytial_relationalizer Boxed boxedRel

public def boxedTwice : Boxed × Boxed := (⟨5⟩, ⟨5⟩)

-- Referential integrity: every tuple endpoint is a real atom. Fails (throws)
-- without the seen-entry reconcile, since the repeated occurrence resolves to
-- the never-emitted pre-allocated id.
open Lean in
#eval show MetaM Unit from do
  let di ← relationalize (mkConst ``boxedTwice)
  let atomIds := di.atoms.toList.map (·.id)
  for r in di.relations do
    for t in r.tuples do
      for a in t.atoms do
        unless atomIds.contains a do
          throwError "dangling endpoint '{a}' in relation '{r.name}' — not an emitted atom"

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

public meta def ropeRel : CustomRelationalizer := fun _ _ => do
  modify fun s : WalkState => s.addAtom { id := "rope", type := "Rope", label := "rope" }
  return "rope"

spytial_spec CoverageFixture.Graph [.hideAtom (selector := "Nat")]
spytial_relationalizer CoverageFixture.Rope ropeRel
spytial_opt_out CoverageFixture.Waived "structural noise, not domain data"

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
error: unknown declaration 'CoverageFixture.DoesNotExist'
-/
#guard_msgs in
spytial_opt_out CoverageFixture.DoesNotExist "x"

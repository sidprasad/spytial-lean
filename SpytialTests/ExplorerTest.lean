import SpytialLean

set_option linter.unusedVariables false

theorem explorerThree (a b c : List Nat) (h : a.length = b.length) : True := by
  let input := (a, (b, c))
  let rotated := ((a, b), c)
  let repaired := (rotated, true)
  spytial input observing [List.length]
  spytial rotated observing [List.length] titled "After rotation"
  spytial repaired observing [List.length] with [hideAtom Bool] titled "After repaint"
  trivial

theorem explorerSingle (n : Nat) : True := by
  spytial (n + 1) titled "One view"
  trivial

theorem explorerBranches (flag : Bool) (xs : List Nat) : True := by
  cases flag with
  | false =>
    let sameName := xs
    spytial sameName titled "False branch"
    trivial
  | true =>
    let sameName := xs
    spytial sameName titled "True branch"
    trivial

theorem explorerRollback (n : Nat) : True := by
  first
  | spytial n titled "Discarded"
    fail
  | spytial n titled "Retained"
  trivial

theorem explorerWithoutInspections : True := by trivial

namespace Nested

theorem qualified (xs : List Nat) : True := by
  spytial xs
  trivial

end Nested

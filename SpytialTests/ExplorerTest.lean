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

/-- Both inspections in the cons branch share `tail`. The fallback has its own scope. -/
def swapFirstTwo : List Nat → List Nat
  | a :: b :: tail =>
    let lower : List Nat := spytial (.cons a tail) titled "New tail"
    spytial (.cons b lower) observing [List.length] with [attribute length] titled "Result"
  | xs => spytial xs titled "Short list"

example (a b : Nat) (tail : List Nat) : swapFirstTwo (a :: b :: tail) = b :: a :: tail := rfl
example : swapFirstTwo [7] = [7] := rfl

def guardedTail (xs : List Nat) : List Nat :=
  if h : xs = [] then
    spytial xs fyi [h] titled "Empty"
  else
    spytial xs titled "Nonempty"

-- Later arguments can still determine implicit types, and the body can call itself.
def mapIdentity (xs : List Nat) : List Nat :=
  List.map (spytial id) xs

example : mapIdentity [1, 2] = [1, 2] := rfl

-- The free variables themselves are known before their types have been inferred.
def inferredElement :=
  List.map (fun x => spytial x) [1, 2]

def inferredList :=
  let xs := []
  let ys := spytial xs
  (1 :: ys : List Nat)

-- The inspected numeral is fully typed, but its displayed context is still being inferred.
def inferredLocalType :=
  let xs := []
  let head := spytial (1 : Nat)
  (head :: xs : List Nat)

def inferredLocalValue :=
  let n : Nat := _
  let result := spytial (7 : Nat)
  let _ : n = 3 := by rfl
  result

example : inferredElement = [1, 2] := rfl
example : inferredList = [1] := rfl
example : inferredLocalType = [1] := rfl
example : inferredLocalValue = 7 := rfl

example : {α : Type} → α → α := spytial @id
def copyList : List Nat → List Nat
  | [] => []
  | x :: xs => spytial (x :: copyList xs)

example : copyList [1, 2] = [1, 2] := rfl

/-- warning: spytial: IYKYK found an inconsistent context; no diagram rendered -/
#guard_msgs in
example (h : (some 1 : Option Nat) = none) : Nat := spytial 0

theorem explorerExclusion (x : Nat) (h : x = 7) : x = 7 := by
  spytial x fyi [h] nvm [h] titled "Omitted"
  spytial x titled "Restored"
  exact h

def termExclusion (x : Nat) (h : x = 7) :=
  spytial x nvm [h]
example (x : Nat) (h : x = 7) : termExclusion x h = x := rfl

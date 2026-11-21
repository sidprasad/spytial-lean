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

-- Macro expansion can expose an inspection inside an asynchronously elaborated theorem.
-- Updating the absent journal must be safe even though the declaration hook did not see it.
local macro "inspect_from_macro " root:term : tactic => `(tactic| spytial $root)

#guard_msgs in
theorem explorerMacro (n : Nat) : True := by
  inspect_from_macro n
  trivial

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

/-- warning: spytial: inconsistent context; see the inspection for conflicts and counterfactuals -/
#guard_msgs in
example (h : (some 1 : Option Nat) = none) : Nat := spytial 0

theorem explorerExclusion (x : Nat) (h : x = 7) : x = 7 := by
  spytial x fyi [h] nvm [h] titled "Omitted"
  spytial x titled "Restored"
  exact h

def termExclusion (x : Nat) (h : x = 7) :=
  spytial x nvm [h]
example (x : Nat) (h : x = 7) : termExclusion x h = x := rfl

theorem explorerFactChanges (x : Nat) (P Q R : Nat → Prop)
    (hpq : P x ∧ Q x) (hr : R x) : True := by
  spytial x nvm [hr] with [tag univ "P witness" lean (P), tag univ "Q witness" lean (Q)]
  spytial x nvm [hpq]
  spytial x
  trivial

theorem explorerBranchFacts (P : Nat → Prop) (h : (∃ x, P x) ∨ (∃ x, P x)) : True := by
  rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
  · spytial x
    trivial
  · spytial x
    trivial

def explorerHeightContext (a b c : List Nat) (x₁ x₂ x₃ x₄ x₅ x₆ : Nat)
    (outer : a.length < b.length) :=
  spytial (a, (b, c)) observing [List.length] with [attribute length, tag univ "Observed length" length]

set_option spytial.source false in
/-- warning: spytial: inconsistent context; see the inspection for conflicts and counterfactuals -/
#guard_msgs in
theorem explorerCounterfactual (x : Nat) (hx : x = 3) (r : ∀ n, n = 3 → n = 4)
    (ignored : False) : True := by
  spytial x fyi [r] nvm [ignored] with [atomStyle Nat (borderStyle "#0066ff")] titled "Conflicting rule"
  spytial x fyi [r] nvm [ignored] nvm [r] with [atomStyle Nat (borderStyle "#0066ff")] titled "Conflicting rule"
  trivial

/-- warning: spytial: inconsistent context; see the inspection for conflicts and counterfactuals -/
#guard_msgs in
theorem explorerIndependentConflicts (x y : Nat) (hx3 : x = 3) (hx4 : 4 = x)
    (hy0 : y = 0) (hy1 : y = 1) : True := by
  spytial x
  trivial

theorem explorerLayoutError (a b : Nat) (P : Nat → Prop) (h : P a) : True := by
  spytial (a, b) with [orientation fst left, hideAtom Nat] titled "Hidden endpoint"
  spytial (a, b) with [orientation fst left] titled "Visible endpoint"
  trivial

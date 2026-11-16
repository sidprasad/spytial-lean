import SpytialLean

/-!
# Aeneas AVL insertion: did the rotation stop the height increase?

Read `insertInLeft` from the recursive return to the test on the left child's
stored balance factor. Then open `insertInLeft_single_spec` at the proof of
`childFactor`. Which of the two cases in `rotateRight` is still possible?

This standalone Lean adaptation follows Aeneas's Rust extraction and its proof at
https://github.com/AeneasVerif/aeneas/blob/1dc8ad31b1b062a77c50e29144a6c7bba955fa09/tests/lean/Avl/Funs.lean#L126
and https://github.com/AeneasVerif/aeneas/blob/1dc8ad31b1b062a77c50e29144a6c7bba955fa09/tests/lean/Avl/Properties.lean#L823 .
It starts just after the recursive call. Empty children, stored signed bytes and
their checked decrement are represented here by an empty constructor, integers and
an explicit range check. The theorem follows the height and balance-factor part
of the single-rotation case of the upstream specification.
-/

namespace AeneasAVL
open SpytialLean

inductive Tree where
  | empty
  | node (left : Tree) (key : Nat) (stored : Int) (right : Tree)

open Tree

def height : Tree → Nat
  | empty => 0
  | node l _ _ r => max (height l) (height r) + 1

def Tree.storedFactor : Tree → Int
  | empty => 0
  | node _ _ bf _ => bf

/-- The proof relates this mathematical quantity to the signed byte in the node. -/
def balanceFactor : Tree → Int
  | empty => 0
  | node l _ _ r => (height r : Int) - (height l : Int)

def Valid : Tree → Prop
  | empty => True
  | t@(node l _ bf r) =>
    Valid l ∧ Valid r ∧ bf = balanceFactor t ∧ -1 ≤ bf ∧ bf ≤ 1

spytial_spec Tree [
  orientation left + right below,
  -- All empty children share one empty value, which can occur on both sides of a parent.
  orientation left.*(left + right) :> (Tree - lean (fun t : Tree => t matches .empty)) left,
  orientation right.*(left + right) :> (Tree - lean (fun t : Tree => t matches .empty)) right,
  align lean (fun a b : Tree => height a = height b) - iden horizontal,
  attribute key
]

def rotateRight (a : Tree) (x : Nat) (bf : Int) (b : Tree) (z : Nat) (d : Tree) : Tree :=
  if bf = 0 then node a x 1 (node b z (-1) d)
  else
    spytial (node a x 0 (node b z 0 d)) observing [height]

def rotateLeftRight (a : Tree) (x : Nat) (inner : Tree) (z : Nat) (d : Tree) : Option Tree :=
  match inner with
  | empty => none
  | node b y bf c =>
    some (node (node a x (if bf > 0 then -1 else 0) b) y 0
      (node c z (if bf < 0 then 1 else 0) d))

/-- Finish the recursive insert. Its Boolean result tells the parent whether its
left subtree grew. The returned Boolean tells the next ancestor the same thing. -/
def insertInLeft (z : Nat) (oldFactor : Int) (d : Tree) (recursive : Bool × Tree) :
    Option (Bool × Tree) := do
  let (grew, left) := recursive
  if !grew then return (false, node left z oldFactor d)
  let updated := oldFactor - 1
  if updated < -128 || updated > 127 then none else
  if updated != -2 then return (updated != 0, node left z updated d)
  match left with
  | empty => none
  | child@(node a x bf b) =>
    -- The parent reached −2. Which field in the updated left child decides the rotation?
    let child := spytial child observing [height]
    if child.storedFactor ≤ 0 then
      -- This guard includes zero. The insertion proof below has more information.
      return (false, rotateRight a x bf b z d)
    else
      let rotated ← rotateLeftRight a x b z d
      return (false, rotated)

/-- At the single-rotation branch, successful growth of an already nonempty
left subtree rules out a zero balance factor. This is the conditional postcondition
of Aeneas's recursive insert; inserting into an empty tree is a separate case. -/
theorem insertInLeft_single_spec (oldLeft a b d : Tree) (x z : Nat) (bf : Int)
    (oldFactor : (height d : Int) - (height oldLeft : Int) = -1)
    (grew : height (node a x bf b) = height oldLeft + 1)
    (recursivePost : 0 < height oldLeft → balanceFactor (node a x bf b) ≠ 0)
    (leftOK : Valid (node a x bf b)) (rightOK : Valid d) (single : bf ≤ 0) :
    let result := node a x 0 (node b z 0 d)
    insertInLeft z (-1) d (true, node a x bf b) = some (false, result) ∧
      Valid result ∧ height result = height oldLeft + 1 := by
  obtain ⟨va, vb, cache, lower, _⟩ := leftOK
  -- The original left side was already one level taller than d, so it existed.
  have nonzero := recursivePost (by omega)
  have childFactor : bf = -1 := by
    -- With only the guard, zero also fits. Compare the stored field with the
    -- computed factor. In the local facts, which value does the recursive call exclude?
    spytial (node a x bf b) observing [height, balanceFactor]
    omega
  subst bf
  simp only [height] at grew
  simp only [balanceFactor] at cache
  have outerHeight : height a = height d + 1 := by omega
  have innerHeight : height b = height d := by omega
  let newRight := node b z 0 d
  let repaired := node a x 0 newRight
  change insertInLeft z (-1) d (true, node a x (-1) b) = some (false, repaired) ∧
    Valid repaired ∧ height repaired = height oldLeft + 1
  have rightHeight : height newRight = height d + 1 := by simp [newRight, height, innerHeight]
  -- Height used to be oldLeft.height + 1. Check the two children of x to see
  -- why this insertion reports false to the next ancestor.
  spytial repaired observing [height]
  constructor
  · rfl
  constructor
  · have vr : Valid newRight := ⟨vb, rightOK, by simp [balanceFactor, innerHeight], by decide, by decide⟩
    exact ⟨va, vr, by simp [balanceFactor, outerHeight, rightHeight], by decide, by decide⟩
  · change max (height a) (height newRight) + 1 = height oldLeft + 1
    omega

end AeneasAVL

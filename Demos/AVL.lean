import SpytialLean

open SpytialLean

/-!
# AVL rebalancing

Course slides on AVL trees draw the same picture again and again: an unbalanced node `N`,
its taller child `C`, and subtrees `T`, `U`, and `V` drawn as triangles. Each node carries
its height and its balance factor. After each rotation, the instructor draws the tree again.
For one example, see Scott Wehrwein's CSCI 241 lecture
(https://facultyweb.cs.wwu.edu/~wehrwes/courses/csci241_23s/lectures/L11/L11B.pdf).

This file makes those pictures from Lean.

1. Define the tree and draw concrete trees with `#spytial`.
2. Write `rebalance` as in the slides, with an inspection at each case.
3. Prove that `rebalance` repairs a node after an insertion. The goal only says
   `Balanced (rebalance …)`. The inspections draw the slide pictures, with heights
   `h`, `h + 1`, … and balance factors computed from the hypotheses.
-/

namespace AVLDemo

/-! ## 1. The data structure -/

inductive Tree where
  | leaf
  | node (left : Tree) (key : Nat) (right : Tree)

def height : Tree → Nat
  | .leaf => 0
  | .node l _ r => max (height l) (height r) + 1

/-- The balance factor, as in the slides: right height minus left height. -/
def bf : Tree → Int
  | .leaf => 0
  | .node l _ r => (height r : Int) - height l

/-- The AVL property: every node has a balance factor of -1, 0, or 1. -/
inductive Balanced : Tree → Prop where
  | leaf : Balanced .leaf
  | node {l r : Tree} {key : Nat} : Balanced l → Balanced r →
      -1 ≤ bf (.node l key r) → bf (.node l key r) ≤ 1 → Balanced (.node l key r)

/-- Insert without rebalancing. -/
def insertBST (k : Nat) : Tree → Tree
  | .leaf => .node .leaf k .leaf
  | .node l x r => if k < x then .node (insertBST k l) x r else .node l x (insertBST k r)

def Tree.isNode : Tree → Bool
  | .node .. => true
  | .leaf => false

-- Draw each node with its key. Red marks a node that breaks the AVL property. Green marks
-- a subtree proved balanced. Each inspection below adds `height` to every box and `bf` to
-- the nodes Lean has opened. A subtree Lean has not opened is one box, like a triangle on
-- the slides.
spytial_spec Tree [
  orientation left left below,
  orientation right right below,
  attribute key,
  edgeStyle left noLabels,
  edgeStyle right noLabels,
  hideAtom Nat,
  hideAtom lean (fun t : Tree => t matches .leaf),
  atomStyle lean (Balanced) (borderStyle "#15803d" 2),
  atomStyle lean (fun t : Tree => bf t < -1 ∨ 1 < bf t)
    (borderStyle "#b91c1c" 2) (fillStyle "#fef2f2")
]

def keys : List Nat → Tree := List.foldl (fun t k => insertBST k t) .leaf

def before : Tree := keys [20, 10, 30, 5, 15, 25, 35, 3, 12, 40]

-- Balanced: every balance factor is -1, 0, or 1.
#spytial before observing [height, bf]
  with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int]

-- Insert 4 as a plain search tree would. Node 5 now has balance factor -2: its left child
-- is two levels taller than its right child. This is Case 2 below.
#spytial insertBST 4 before observing [height, bf]
  with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int]

/-! ## 2. Rebalancing

The slides give this pseudocode.

```text
rebalance(n):
  if bal(n) < -1:
    if bal(n.left) < 0: case 1     -- right rotate n
    else:               case 2     -- left rotate n.left, then right rotate n
  else if bal(n) > 1:
    if bal(n.right) < 0: case 3    -- right rotate n.right, then left rotate n
    else:                case 4    -- left rotate n
```

Cases 3 and 4 mirror cases 1 and 2. Place the cursor on `rebalance` to step through its
inspections. Each one draws the tree a line of code builds. Inside the function Lean knows
only the branch conditions, so these pictures show shape, not heights. Part 3 adds the
facts that hold after an insertion.
-/

def rotateRight : Tree → Tree
  | .node (.node T c U) n V => .node T c (.node U n V)
  | t => t

def rotateLeft : Tree → Tree
  | .node V n (.node T c U) => .node (.node V n T) c U
  | t => t

/-- Left rotate the left child, as in "left rotate C". -/
def rotateLeftChild : Tree → Tree
  | .node C n V => .node (rotateLeft C) n V
  | t => t

def rebalance : Tree → Tree
  | .leaf => .leaf
  | .node C n V =>
    if bf (.node C n V) < -1 then
      match C with
      | .leaf => .node .leaf n V
      | .node T c U =>
        if bf (.node T c U) < 0 then
          let N := spytial (Tree.node (.node T c U) n V) titled "Case 1"
          spytial (rotateRight N) titled "Case 1: right rotate N"
        else
          match U with
          | .leaf => .node (.node T c .leaf) n V
          | .node X u Y =>
            let N := spytial (Tree.node (.node T c (.node X u Y)) n V) titled "Case 2"
            let N := spytial (rotateLeftChild N) titled "Case 2: left rotate C"
            spytial (rotateRight N) titled "Case 2: right rotate N"
    else if 1 < bf (.node C n V) then
      if bf V < 0 then rotateLeft (.node C n (rotateRight V))
      else rotateLeft (.node C n V)
    else .node C n V

/-- AVL insertion: insert as in a search tree, then rebalance on the way back up. -/
def insert (k : Nat) : Tree → Tree
  | .leaf => .node .leaf k .leaf
  | .node l x r =>
    if k < x then rebalance (.node (insert k l) x r) else rebalance (.node l x (insert k r))

-- The same insertion with rebalancing. Node 4 has moved up between 3 and 5.
#spytial insert 4 before observing [height, bf]
  with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int]

/-! ## 3. Rebalancing after an insertion

An insertion has made `C` two levels taller than `V`. Name `V`'s height `h`. Both subtrees
are AVL trees, and `C` grew, so it leans to one side: its balance factor is not 0.

The goal mentions none of `T`, `U`, `h + 1`, or `-2`. Read the inspections in order: they
are the slides for Cases 1 and 2, drawn from the hypotheses for every tree that fits.
-/

theorem Balanced.children {l r : Tree} {key : Nat} (b : Balanced (.node l key r)) :
    Balanced l ∧ Balanced r ∧ -1 ≤ bf (.node l key r) ∧ bf (.node l key r) ≤ 1 := by
  cases b with
  | node bl br lo hi => exact ⟨bl, br, lo, hi⟩

/-- Build a balanced node from the children's heights. -/
theorem Balanced.mk {l r : Tree} {key : Nat} (bl : Balanced l) (br : Balanced r)
    (fits : height l ≤ height r + 1 ∧ height r ≤ height l + 1) : Balanced (.node l key r) :=
  .node bl br (by simp only [bf]; omega) (by simp only [bf]; omega)

theorem rebalance_after_insert (C V : Tree) (n h : Nat)
    (bC : Balanced C) (bV : Balanced V) (hC : height C = h + 2) (hV : height V = h)
    (leans : bf C ≠ 0) :
    Balanced (rebalance (.node C n V)) := by
  -- N's left child is two levels taller. C is still a closed triangle.
  spytial (Tree.node C n V) observing [height, bf]
    with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int,
      hideField Balanced]
    titled "After the insertion"
  cases C with
  | leaf => simp [height] at hC
  | node T c U =>
    obtain ⟨bT, bU, lo, hi⟩ := bC.children
    simp only [bf, height] at hC lo hi leans
    by_cases outer : bf (.node T c U) < 0
    · -- Case 1: C leans left, so T is the tall grandchild.
      simp only [bf] at outer
      have hT : height T = h + 1 := by omega
      have hU : height U = h := by omega
      clear hC lo hi leans outer bC
      let N := Tree.node (.node T c U) n V
      spytial N observing [height, bf]
        with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int,
          hideField Balanced]
        titled "Case 1"
      let rotated := rotateRight N
      spytial rotated observing [height, bf]
        with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int,
          hideField Balanced]
        titled "Case 1: right rotate N"
      have step : rebalance N = rotated := by
        simp only [N, rebalance]
        rw [if_pos (by simp only [bf, height]; omega), if_pos (by simp only [bf]; omega)]
      rw [step]
      exact .mk bT (.mk bU bV (by omega)) (by simp only [height]; omega)
    · -- Case 2: C leans right, so U is the tall grandchild. Open it.
      simp only [bf] at outer
      have hU : height U = h + 1 := by omega
      have hT : height T = h := by omega
      cases U with
      | leaf => simp [height] at hU
      | node X u Y =>
        obtain ⟨bX, bY, lo', hi'⟩ := bU.children
        simp only [bf, height] at hU lo' hi'
        -- X and Y each have height h or h - 1. Neither is fixed.
        have hX : height X ≤ h ∧ h ≤ height X + 1 := by omega
        have hY : height Y ≤ h ∧ h ≤ height Y + 1 := by omega
        have hmax : max (height X) (height Y) = h := by omega
        clear hC lo hi leans outer bC hU lo' hi' bU
        let N := Tree.node (.node T c (.node X u Y)) n V
        spytial N observing [height, bf]
          with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int,
            hideField Balanced]
          titled "Case 2"
        let middle := rotateLeftChild N
        spytial middle observing [height, bf]
          with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int,
            hideField Balanced]
          titled "Case 2: left rotate C"
        let rotated := rotateRight middle
        spytial rotated observing [height, bf]
          with [.., attribute height, attribute bf selector: lean (Tree.isNode), hideAtom Int,
            hideField Balanced]
          titled "Case 2: right rotate N"
        have step : rebalance N = rotated := by
          have hU' : height (.node X u Y) = h + 1 := by simp only [height]; omega
          have hC' : height (.node T c (.node X u Y)) = h + 2 := by simp only [height]; omega
          simp only [N, rebalance]
          rw [if_pos (by simp only [bf]; rw [hC', hV]; omega),
            if_neg (by simp only [bf]; rw [hU', hT]; omega)]
        rw [step]
        exact .mk (.mk bT bX (by omega)) (.mk bY bV (by omega)) (by simp only [height]; omega)

end AVLDemo

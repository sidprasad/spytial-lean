import SpytialLean

open SpytialLean

/-!
# AVL rebalancing

Course slides on AVL trees draw the same picture again and again: an unbalanced root,
its taller child, and the unopened subtrees drawn as triangles. Each node carries
its height and its balance factor. After each rotation, the instructor draws the tree again.
For one example, see Scott Wehrwein's CSCI 241 lecture
(https://facultyweb.cs.wwu.edu/~wehrwes/courses/csci241_23s/lectures/L11/L11B.pdf).

This file makes those pictures from Lean. The companion walkthrough in `Demos/AVL.md`
starts at the branch where the reader can predict which key will become the new root.

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

-- Label each opened node with its key. An unopened subtree gets one box, like a triangle
-- on the slides. The proof inspections add heights and balance factors.
spytial_spec Tree [
  -- Position visible children. Empty child slots all point to the same hidden leaf.
  orientation inspectedRoot.*(left + right) <: left :> {t : Tree | @:t != leaf} left below,
  orientation inspectedRoot.*(left + right) <: right :> {t : Tree | @:t != leaf} right below,
  align let children = inspectedRoot.*(left + right) <: (left + right)
      :> {t : Tree | @:t != leaf} | ~children.children - iden horizontal,
  attribute key,
  hideAtom univ - inspectedRoot.*(left + right),
  -- Suppress the shared empty child. An inspection of the empty tree itself still has a root.
  hideAtom {t : Tree | @:t = leaf} - inspectedRoot,
]

def keys : List Nat → Tree := List.foldl (fun t k => insertBST k t) .leaf

def before : Tree := keys [20, 10, 30, 5, 15, 25, 35, 3, 12, 40]

-- Balanced: every balance factor is -1, 0, or 1.
#spytial before observing [height, bf]
  with [.., attribute height, attribute bf, hideAtom Int]

-- Insert 4 as a plain search tree would. Node 5 now has balance factor -2: its left child
-- is two levels taller than its right child. This is Case 2 below.
#spytial insertBST 4 before observing [height, bf]
  with [.., attribute height, attribute bf selector: key.univ, hideAtom Int]

/-! ## 2. Rebalancing

The slides give this pseudocode.

```text
rebalance(tree):
  if bal(tree) < -1:
    if bal(tree.left) < 0: case 1     -- rotate the root right
    else:                  case 2     -- rotate the left child left, then the root right
  else if bal(tree) > 1:
    if bal(tree.right) < 0: case 3    -- rotate the right child right, then the root left
    else:                   case 4    -- rotate the root left
```

Cases 3 and 4 mirror cases 1 and 2. Place the cursor on `rebalance` to step through its
inspections. The named match equations connect the input and its children to their
patterns inside each branch. A requested height can still contain a symbolic maximum.
Part 3 supplies the height facts that hold after an insertion.
-/

def rotateRight : Tree → Tree
  | .node (.node left pivotKey middle) rootKey right =>
    .node left pivotKey (.node middle rootKey right)
  | tree => tree

def rotateLeft : Tree → Tree
  | .node left rootKey (.node middle pivotKey right) =>
    .node (.node left rootKey middle) pivotKey right
  | tree => tree

/-- Rotate the left child left and reattach it to the root. -/
def rotateLeftChild : Tree → Tree
  | .node left rootKey right => .node (rotateLeft left) rootKey right
  | tree => tree

-- The inspections use the match equations and field names from the local context.
set_option linter.unusedVariables false in
def rebalance (tree : Tree) : Tree :=
  match rootShape : tree with
  | .leaf => tree
  | .node left rootKey right =>
    if bf tree < -1 then
      match leftShape : left with
      | .leaf => tree
      | .node outer leftKey inner =>
        let leftFactor := bf (spytial left observing [height] with [.., attribute height])
        if leftFactor < 0 then
          let repaired := rotateRight (spytial tree)
          spytial repaired observing [height, bf]
            with [.., attribute height, attribute bf selector: key.univ]
        else
          match innerShape : inner with
          | .leaf => tree
          | .node pivotLeft pivotKey pivotRight =>
            let leftChildRotated := rotateLeftChild (spytial tree)
            let repaired := rotateRight (spytial leftChildRotated)
            spytial repaired
    else if 1 < bf tree then
      if bf right < 0 then rotateLeft (.node left rootKey (rotateRight right))
      else rotateLeft tree
    else tree

/-- AVL insertion: insert as in a search tree, then rebalance on the way back up. -/
def insert (k : Nat) : Tree → Tree
  | .leaf => .node .leaf k .leaf
  | .node l x r =>
    if k < x then rebalance (.node (insert k l) x r) else rebalance (.node l x (insert k r))

-- The same insertion with rebalancing. Node 4 has moved up between 3 and 5.
#spytial insert 4 before observing [height, bf]
  with [.., attribute height, attribute bf selector: key.univ, hideAtom Int]

/-! ## 3. Rebalancing after an insertion

This local repair theorem takes the post-insertion facts as hypotheses. Both children
are balanced. The left subtree leans and is two levels taller than the right subtree.

Compare the two inspections that ask whether the left child can become the root.
Both inspect the same bound tree before the proof names its repair.
-/

theorem Balanced.children {l r : Tree} {key : Nat} (b : Balanced (.node l key r)) :
    Balanced l ∧ Balanced r ∧ -1 ≤ bf (.node l key r) ∧ bf (.node l key r) ≤ 1 := by
  cases b with
  | node bl br lo hi => exact ⟨bl, br, lo, hi⟩

/-- Build a balanced node from the children's heights. -/
theorem Balanced.mk {l r : Tree} {key : Nat} (bl : Balanced l) (br : Balanced r)
    (fits : height l ≤ height r + 1 ∧ height r ≤ height l + 1) : Balanced (.node l key r) :=
  .node bl br (by simp only [bf]; omega) (by simp only [bf]; omega)

theorem rebalance_after_insert (left right : Tree) (rootKey baseHeight : Nat)
    (leftBalanced : Balanced left) (rightBalanced : Balanced right)
    (leftHeight : height left = baseHeight + 2) (rightHeight : height right = baseHeight)
    (leans : bf left ≠ 0) :
    Balanced (rebalance (.node left rootKey right)) := by
  let tree := Tree.node left rootKey right
  change Balanced (rebalance tree)
  spytial tree observing [height, bf]
    with [.., attribute height, attribute bf, hideAtom Int]
    titled "After the insertion"
  cases leftShape : left with
  | leaf => simp [leftShape, height] at leftHeight
  | node outer leftKey inner =>
    rw [leftShape] at leftBalanced leftHeight leans
    obtain ⟨outerBalanced, innerBalanced, lo, hi⟩ := leftBalanced.children
    have levels : max (height outer) (height inner) + 1 = baseHeight + 2 := leftHeight
    simp only [bf] at lo hi leans
    by_cases outerTaller : height inner < height outer
    · -- The outside grandchild is taller.
      have outerHeight : height outer = baseHeight + 1 := by omega
      have innerHeight : height inner = baseHeight := by omega
      clear levels lo hi leans outerTaller leftBalanced
      -- Predict the new root before looking at the return expression.
      spytial tree observing [height, bf]
        with [.., attribute height, attribute bf, hideAtom Int]
        titled "Outer subtree taller. Can the left child become the root?"
      let rebalanced := rotateRight tree
      spytial rebalanced observing [height, bf]
        with [.., attribute height, attribute bf selector: key.univ, hideAtom Int,
          hideField Balanced]
      subst left
      have step : rebalance tree = rebalanced := by
        simp only [tree, rebalance]
        rw [if_pos (by simp only [bf, height]; omega), if_pos (by simp only [bf]; omega)]
      rw [step]
      exact .mk outerBalanced (.mk innerBalanced rightBalanced (by omega))
        (by simp only [height]; omega)
    · -- The inside grandchild is taller.
      have innerHeight : height inner = baseHeight + 1 := by omega
      have outerHeight : height outer = baseHeight := by omega
      clear levels lo hi leans outerTaller leftBalanced
      spytial tree observing [height, bf]
        with [.., attribute height, attribute bf selector: key.univ, hideAtom Int,
          hideField Balanced]
        titled "Inner subtree taller. Can the left child become the root?"
      cases innerShape : inner with
      | leaf => simp [innerShape, height] at innerHeight
      | node pivotLeft pivotKey pivotRight =>
        rw [innerShape] at innerBalanced innerHeight
        obtain ⟨pivotLeftBalanced, pivotRightBalanced, lo', hi'⟩ := innerBalanced.children
        have pivotMax : max (height pivotLeft) (height pivotRight) = baseHeight :=
          Nat.succ.inj innerHeight
        simp only [bf] at lo' hi'
        -- Either side of the pivot may be shorter by one.
        have pivotLeftFits : height pivotLeft ≤ baseHeight ∧
            baseHeight ≤ height pivotLeft + 1 := by omega
        have pivotRightFits : height pivotRight ≤ baseHeight ∧
            baseHeight ≤ height pivotRight + 1 := by omega
        clear lo' hi' innerBalanced
        spytial tree observing [height, bf]
          with [.., attribute height, attribute bf selector: key.univ, hideAtom Int,
            hideField Balanced]
        let leftChildRotated := rotateLeftChild tree
        spytial leftChildRotated observing [height, bf]
          with [.., attribute height, attribute bf selector: key.univ, hideAtom Int,
            hideField Balanced]
        let rebalanced := rotateRight leftChildRotated
        spytial rebalanced observing [height, bf]
          with [.., attribute height, attribute bf selector: inspectedRoot, hideAtom Int,
            hideField Balanced]
          titled "Where did the pivot’s two subtrees go?"
        subst left
        subst inner
        have step : rebalance tree = rebalanced := by
          simp only [tree, rebalance]
          rw [if_pos (by simp only [bf]; rw [leftHeight, rightHeight]; omega),
            if_neg (by simp only [bf]; rw [innerHeight, outerHeight]; omega)]
        rw [step]
        exact .mk (.mk outerBalanced pivotLeftBalanced (by omega))
          (.mk pivotRightBalanced rightBalanced (by omega)) (by simp only [height]; omega)

/-- Try the outer-heavy branch's repair under the inner-heavy branch's height facts. -/
theorem singleRotation_fails (outer inner right : Tree) (leftKey rootKey baseHeight : Nat)
    (outerHeight : height outer = baseHeight) (innerHeight : height inner = baseHeight + 1)
    (rightHeight : height right = baseHeight) :
    let candidate := rotateRight (.node (.node outer leftKey inner) rootKey right)
    ¬ Balanced candidate := by
  intro candidate
  spytial candidate observing [height, bf]
    with [.., attribute height, attribute bf selector: key.univ, hideAtom Int]
    titled "What is the balance factor at leftKey?"
  intro ok
  have fits := ok.children.2.2.2
  simp only [bf, height] at fits
  omega

end AVLDemo

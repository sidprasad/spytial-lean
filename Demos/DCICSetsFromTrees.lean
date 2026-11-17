import Demos.AVL

/-!
# Can a subtree really have height `k − 2`?

The last exercise of DCIC’s *Sets from Trees*, §18.2.3,
asks whether a double rotation can leave a height gap of two. The answer depends on **where
in the insertion** we inspect the tree. Start at the three `#spytial` commands. Then select
the name of either repair theorem in the infoview and expand **Spytial inspections**.
[DCIC chapter](https://dcic-world.org/2025-08-27/sets-from-trees.html) ·
[Illustrated walkthrough](DCICSetsFromTrees.md)

We use DCIC’s names. The old root is `p`, its left child is `q`, and `q.right` has root `r`.
The four subtrees, in key order, are `A`, `B₁`, `B₂`, and `C`. Let `k` be the height of `C`.
We count the empty tree as height zero and use DCIC’s balance factor, left height minus right.
-/

namespace DCICSetsFromTrees

open AVLDemo (Tree height Balanced rotateLeftChild rotateRight rebalance)
open AVLDemo.Tree
open SpytialLean

def factor : Tree → Int
  | leaf => 0
  | node l _ r => (height l : Int) - height r

def inorder : Tree → List Nat
  | leaf => []
  | node l key r => inorder l ++ key :: inorder r

/-- Set insertion. Pass `id` for ordinary BST insertion or `rebalance` for AVL insertion. -/
def insertWith (repair : Tree → Tree) (key : Nat) : Tree → Tree
  | leaf => node leaf key leaf
  | t@(node l x r) =>
    if key < x then repair (node (insertWith repair key l) x r)
    else if x < key then repair (node l x (insertWith repair key r))
    else t

def doubleRotate (t : Tree) : Tree := rotateRight (rotateLeftChild t)

-- Keep the four subtrees in key order. Empty children share one hidden leaf.
spytial_ops treeView : Tree [
  orientation inspectedRoot.*(left + right) <: left :> {t : Tree | @:t != leaf} left below,
  orientation inspectedRoot.*(left + right) <: right :> {t : Tree | @:t != leaf} right below,
  align let children = inspectedRoot.*(left + right) <: (left + right)
      :> {t : Tree | @:t != leaf} | ~children.children - iden horizontal,
  hideAtom univ - inspectedRoot.*(left + right),
  hideAtom {t : Tree | @:t = leaf},
  attribute key,
  atomStyle Tree (borderStyle "#475569" 1),
  atomStyle lean (fun t : Tree => factor t = -2) + lean (fun t : Tree => factor t = 2)
    (fillStyle "#fecaca")
]

/-! ## Insert 4 and choose where to rotate

Here `p = 8`, `q = 3`, `r = 6`, and `k = 2`. Follow the insertion back up through
`5, 6, 3, 8`. Which node first has a height gap of two?
-/

def before : Tree := [8, 3, 10, 2, 6, 9, 1, 5].foldl (fun t x => insertWith id x t) leaf
def raw : Tree := insertWith id 4 before

-- At 6 the left child has height 2. Its empty right child has height 0, exactly k − 2.
#spytial raw observing [height, factor] with [..treeView, attribute height, attribute factor]

-- Try DCIC’s double rotation at 8. Read the factor at the new root, then at its right child.
#spytial doubleRotate raw observing [height, factor]
  with [..treeView, attribute height, attribute factor]

-- Run the recursive algorithm on the same input. Which of 6 and 8 actually needs a rotation?
#spytial insertWith rebalance 4 before observing [height, factor]
  with [..treeView, attribute height, attribute factor]

example : Balanced before := by
  repeat first | apply Balanced.node | exact Balanced.leaf | decide

example : Balanced (insertWith rebalance 4 before) := by
  repeat first | apply Balanced.node | exact Balanced.leaf | decide

example : inorder (insertWith rebalance 4 before) = [1, 2, 3, 4, 5, 6, 8, 9, 10] := rfl

/-! ## What goes wrong if we rotate too high?

Suppose `B₂` is the short subtree. Follow its edge through the rotation. Which subtree
becomes its new sibling? We can answer for every `k ≥ 2` without choosing any keys.
-/

theorem doubleRotate_inorder (A B₁ B₂ C : Tree) (p q r : Nat) :
    let t := node (node A q (node B₁ r B₂)) p C
    inorder (doubleRotate t) = inorder t := by
  simp [doubleRotate, rotateLeftChild, AVLDemo.rotateLeft, rotateRight, inorder, List.append_assoc]

theorem premature_rotation (A B₁ B₂ C : Tree) (p q r k : Nat) (hk : 2 ≤ k)
    (hA : height A = k) (h₁ : height B₁ = k) (h₂ : height B₂ = k - 2) (hC : height C = k) :
    let t := node (node A q (node B₁ r B₂)) p C
    factor (doubleRotate t) = 0 ∧ ¬ Balanced (doubleRotate t) := by
  -- Heights are natural numbers. With k ≥ 2, the integer factor sees the full gap.
  have short : ((k - 2 : Nat) : Int) = (k : Int) - 2 := by omega
  let t := node (node A q (node B₁ r B₂)) p C
  spytial t observing [height, factor]
    with [..treeView, attribute height, attribute factor selector: key.univ]
    titled "Which gap would insertion reach first?"
  spytial (doubleRotate t) observing [height, factor]
    with [..treeView, attribute height, attribute factor selector: key.univ]
    titled "The new root has factor zero. Where did the short subtree go?"
  constructor
  · change (height (node A q B₁) : Int) - height (node B₂ p C) = 0
    simp only [height, hA, h₁, h₂, hC]
    omega
  · intro ok
    have atP : Balanced (node B₂ p C) := ok.children.2.1
    have bound := atP.children.2.2.2
    simp only [AVLDemo.bf, h₂, hC] at bound
    omega

-- The raw insertion above instantiates exactly this family, with k = 2.
example : factor (doubleRotate raw) = 0 ∧ ¬ Balanced (doubleRotate raw) :=
  premature_rotation _ _ _ _ _ _ _ 2 (by decide) rfl rfl rfl rfl

/-! ## What does the recursive return tell us?

Now pause when insertion actually reaches `p`. Its two children have already been repaired.
The left child is two levels taller than `C` and leans inward. These are the branch conditions
that choose a double rotation. The proof derives the allowed heights of `B₁` and `B₂` from them.
-/

theorem bottomUp_rotation (A B₁ B₂ C : Tree) (p q r k : Nat)
    (leftOK : Balanced (node A q (node B₁ r B₂))) (rightOK : Balanced C)
    (hC : height C = k) (overflow : height (node A q (node B₁ r B₂)) = k + 2)
    (inward : height A < height (node B₁ r B₂)) :
    let t := node (node A q (node B₁ r B₂)) p C
    rebalance t = doubleRotate t ∧ Balanced (doubleRotate t) ∧ height (doubleRotate t) = k + 2 ∧
      inorder (doubleRotate t) = inorder t := by
  let t := node (node A q (node B₁ r B₂)) p C
  have chosen : rebalance t = doubleRotate t := by
    have atRoot : AVLDemo.bf t < -1 := by
      change (height C : Int) - height (node A q (node B₁ r B₂)) < -1
      omega
    have atLeft : ¬ AVLDemo.bf (node A q (node B₁ r B₂)) < 0 := by
      simp only [AVLDemo.bf]
      omega
    simp only [t, rebalance, if_pos atRoot, if_neg atLeft, doubleRotate, rotateLeftChild,
      AVLDemo.rotateLeft, rotateRight]
  obtain ⟨aOK, pivotOK, qLo, qHi⟩ := leftOK.children
  obtain ⟨b₁OK, b₂OK, rLo, rHi⟩ := pivotOK.children
  simp only [AVLDemo.bf, height] at qLo qHi rLo rHi overflow inward
  have hA : height A = k := by omega
  have tallest : max (height B₁) (height B₂) = k := by omega
  -- Both short-side bounds include k = 0 and avoid truncated subtraction on naturals.
  have fits₁ : height B₁ ≤ k ∧ k ≤ height B₁ + 1 := by omega
  have fits₂ : height B₂ ≤ k ∧ k ≤ height B₂ + 1 := by omega
  spytial (doubleRotate t) observing [height, factor]
    with [..treeView, attribute height, attribute factor selector: inspectedRoot,
      hideField Balanced]
    titled "What height can we predict for each new child?"
  have atQ : Balanced (node A q B₁) := .mk aOK b₁OK (by omega)
  have atP : Balanced (node B₂ p C) := .mk b₂OK rightOK (by omega)
  have hQ : height (node A q B₁) = k + 1 := by simp only [height]; omega
  have hP : height (node B₂ p C) = k + 1 := by simp only [height]; omega
  refine ⟨chosen, .mk atQ atP (by omega), ?_, doubleRotate_inorder ..⟩
  change max (height (node A q B₁)) (height (node B₂ p C)) + 1 = k + 2
  simp [hQ, hP]

end DCICSetsFromTrees

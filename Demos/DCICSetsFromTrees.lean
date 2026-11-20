import SpytialLean

/-!
# DCIC §18.2.3 · A Fine Balance: Tree Surgery

Searching a binary search tree follows one branch. If successive insertions make a chain,
search can still visit every key. DCIC asks how to keep the tree shallow while preserving the
order that makes search possible. Its balance factor is **left height minus right height**.
A balanced tree has factor −1, 0, or +1 at every node.

Start with a balanced tree and insert one key on the left. Only one path can grow, by at most
one level. A node on that path can therefore reach +2. The algorithm checks the nodes on the
way **back up**. Keep that timing in mind when the last exercise asks whether a rotation failed.

Read each sketch with the cursor on the `spytial` immediately below it. The letters `p, q, r`
are keys and the capitals are whole subtrees. DCIC writes a node as `node(p, l, r)`.
Lean’s `node l p r` puts the same key between its children.
[Read §18.2.3 in DCIC](https://dcic-world.org/2025-08-27/sets-from-trees.html#%28part._sets-from-balanced-trees%29).
-/

namespace DCICSetsFromTrees

open SpytialLean

inductive Tree where
  | leaf
  | node (left : Tree) (key : Nat) (right : Tree)

open Tree

/-! We count an empty leaf as height 0 and a singleton as height 1. Only differences of
heights enter the balance factor. Slate fill marks an unopened subtree in the infoview.
-/

def height : Tree → Nat
  | leaf => 0
  | node l _ r => max (height l) (height r) + 1

/-- The chapter counts left height minus right height. -/
def factor : Tree → Int
  | leaf => 0
  | node l _ r => (height l : Int) - height r

def Balanced : Tree → Prop
  | leaf => True
  | node l _ r => Balanced l ∧ Balanced r ∧ height l ≤ height r + 1 ∧ height r ≤ height l + 1

/-- Every key in the subtree is strictly less than the bound. -/
def keysLt : Tree → Nat → Prop
  | leaf, _ => True
  | node l x r, b => keysLt l b ∧ x < b ∧ keysLt r b

/-- Every key in the subtree is strictly greater than the bound. -/
def keysGt : Tree → Nat → Prop
  | leaf, _ => True
  | node l x r, b => keysGt l b ∧ b < x ∧ keysGt r b

def BST : Tree → Prop
  | leaf => True
  | node l x r => BST l ∧ BST r ∧ keysLt l x ∧ keysGt r x

private def hasHeightGap : Tree → Prop
  | leaf => False
  | node l _ r => height l + 2 ≤ height r ∨ height r + 2 ≤ height l

spytial_spec Tree [
  -- Place nonempty children to the left and right of their parent on the next row.
  orientation inspectedRoot.*(left + right) <: left :> {t : Tree | @:t != leaf} left below,
  orientation inspectedRoot.*(left + right) <: right :> {t : Tree | @:t != leaf} right below,
  align let children = inspectedRoot.*(left + right) <: (left + right)
      :> {t : Tree | @:t != leaf} | ~children.children - iden horizontal,
  -- Keep the inspected tree and hide its empty children.
  hideAtom univ - inspectedRoot.*(left + right),
  hideAtom {t : Tree | @:t = leaf} - inspectedRoot,
  attribute key,
  attribute height,
  attribute factor selector: key.univ,
  -- Shade unopened subtrees in slate and highlight gaps of at least two in pink.
  atomStyle {t : Tree | no t.key && @:t != leaf} (fillStyle "#e2e8f0"),
  atomStyle lean (hasHeightGap) (fillStyle "#fecaca"),
  -- Outline the inspected root in blue and proven balanced descendants in green.
  atomStyle inspectedRoot (borderStyle "#1d4ed8" 4),
  atomStyle lean (Balanced) - inspectedRoot (borderStyle "#28705a" 2),
  atomStyle Tree - inspectedRoot - lean (Balanced) (borderStyle "#475569" 1),
  -- Make a node's label purple when Lean can establish BST for the subtree rooted there.
  atomStyle lean (BST) (textStyle "#6d28d9"),
  -- Use key bounds to explain where unopened subtrees can move during a rotation.
  tag {t : Tree | no t.key && @:t != leaf} "Every key >" lean (keysGt),
  tag {t : Tree | no t.key && @:t != leaf} "Every key <" lean (keysLt)
]

/-! Why does balance keep searches short? In a balanced tree of height `h ≥ 2`, one child
has height `h − 1` and the other has height at least `h − 2`. Thus every two levels of
height at least double the minimum number of nodes. Search follows one path of logarithmic length.

In DCIC’s schematic, let `C`, the right subtree of `p`, have height `k`. Before insertion
the left child `q` had height `k + 1`. For `p` to reach factor +2, `q` must grow to
height `k + 2`. That puts one of `A` and `B` at height
`k + 1`. The other still has its old height (either `k` or `k − 1`), because insertion took
just one branch at `q`. These are the chapter’s two cases.
-/

theorem gapAtRoot (A B C : Tree) (p q k : Nat)
    (grew : height (node A q B) = k + 2) (hC : height C = k) :
    factor (node (node A q B) p C) = 2 := by
  have children : max (height A) (height B) = k + 1 := by
    simpa [height, Nat.add_assoc] using grew
  /- The common starting point for both cases, just after growth on the left.

           p
          / \
         q   C
        / \
       A   B
  -/
  spytial (node (node A q B) p C) observing [height, factor]
  simp only [factor, grew, hC]
  omega

/-! DCIC writes `T < a` when every key in subtree `T` is less than `a`. We write `keysLt T a`
in Lean and “Every key < a” in the schematic. The other direction, `a < T`, is `keysGt T a`.
So `q < B < p` gives `B` two labels, “Every key > q” and “Every key < p”.
-/

/-! ## 18.2.3.1 · Left-Left Case

Suppose `A` grew. When the algorithm checks `p`, the call on its left has returned a balanced
subtree and its right subtree is untouched. These are `leftOK` and `rightOK`. Open `A` to see its key
`r`, then find a place for `B` if `q` becomes the root. The inspected root has a blue outline.
Green outlines mark descendants whose balance Lean can establish. Purple node names mark
subtrees whose search-tree ordering Lean can establish, and `BST` loops show the ordering facts.
[DCIC’s left-left case](https://dcic-world.org/2025-08-27/sets-from-trees.html#%28part._.Left-.Left_.Case%29).
-/

def rotateRight : Tree → Tree
  | node (node A q B) p C => node A q (node B p C)
  | t => t

private theorem keysGt_weaken {t : Tree} {a b : Nat} (ab : a < b) (h : keysGt t b) : keysGt t a := by
  induction t with
  | leaf => trivial
  | node l x r il ir => exact ⟨il h.1, Nat.lt_trans ab h.2.1, ir h.2.2⟩

/-- A right rotation preserves search-tree order. -/
theorem ordered_right {A B C : Tree} {p q : Nat}
    (ok : BST (node (node A q B) p C)) : BST (rotateRight (node (node A q B) p C)) := by
  obtain ⟨⟨a, b, aq, qb⟩, c, ⟨_, qp, bp⟩, pc⟩ := ok
  exact ⟨a, ⟨b, c, bp, pc⟩, aq, qb, qp, keysGt_weaken qp pc⟩

theorem leftLeft (A B C : Tree) (p q k : Nat) (ordered : BST (node (node A q B) p C))
    (leftOK : Balanced (node A q B)) (rightOK : Balanced C)
    (taller : height A = k + 1) (outer : height B < height A) (hC : height C = k) :
    let t := node (node A q B) p C
    BST (rotateRight t) ∧ Balanced (rotateRight t) := by
  let t := node (node A q B) p C
  spytial t observing [height]
  -- A has height k + 1, so it has a root r and two children.
  cases A with
  | leaf => simp [height] at taller
  | node A₁ r A₂ =>
    /- Open A. Read the bounds on the four unopened subtrees.

                 p
                / \
               q   C
              / \
             r   B
            / \
           A₁  A₂

       A₁ < r       r < A₂ < q       q < B < p       p < C

       All six comparisons come from the hypothesis `ordered`. In particular, A₂ inherits
       its lower bound from r and its upper bound from q. Since A has height k + 1, its
       taller child has height k. Both A₁ and A₂ stay attached to r in the rotation. -/
    spytial t

    /- Promote q. The keys in B must stay greater than q and less than p, so B becomes p’s left child.

                 q
               /   \
              r     p
             / \   / \
            A₁ A₂  B   C
    -/
    spytial (rotateRight t)
    -- Since q returned balanced with A at height k + 1, B must have height k here.
    -- The new p has children B and C of height k. Its height matches A at k + 1.
    obtain ⟨aOK, bOK, ab, _⟩ := leftOK
    have hB : height B = k := by omega
    have pOK : Balanced (node B p C) := ⟨bOK, rightOK, by omega, by omega⟩
    have hp : height (node B p C) = k + 1 := by simp [height, hB, hC]
    have hq : height (rotateRight t) = k + 2 := by
      change max (height (node A₁ r A₂)) (height (node B p C)) + 1 = k + 2
      rw [taller, hp, Nat.max_self]
    -- Check both children of q at height k + 1. Since q < p < C, C also exceeds the new root.
    have qp : q < p := ordered.2.2.1.2.1
    have pc : keysGt C p := ordered.2.2.2
    spytial (rotateRight t) fyi [keysGt_weaken (t := C) qp]
    exact ⟨ordered_right ordered, aOK, pOK, by omega, by omega⟩

/-! ## 18.2.3.2 · Left-Right Case

Now suppose `B` grew. Its root `r` lies between `q` and `p`. Follow the two rotations in
order. The first makes `r` the left child of `p`. The second makes `r` the root of the
whole tree. Each step must preserve the same four intervals.
[DCIC’s left-right case](https://dcic-world.org/2025-08-27/sets-from-trees.html#%28part._.Left-.Right_.Case%29).
-/

def rotateLeft : Tree → Tree
  | node A q (node B₁ r B₂) => node (node A q B₁) r B₂
  | t => t

def rotateLeftChild : Tree → Tree
  | node l p C => node (rotateLeft l) p C
  | leaf => leaf

def doubleRotate (t : Tree) : Tree := rotateRight (rotateLeftChild t)

private theorem keysLt_weaken {t : Tree} {a b : Nat} (ab : a < b) (h : keysLt t a) : keysLt t b := by
  induction t with
  | leaf => trivial
  | node l x r il ir => exact ⟨il h.1, Nat.lt_trans h.2.1 ab, ir h.2.2⟩

private theorem ordered_left {A B C : Tree} {p q : Nat}
    (ok : BST (node A p (node B q C))) : BST (rotateLeft (node A p (node B q C))) := by
  obtain ⟨a, ⟨b, c, bq, qc⟩, ap, ⟨pb, pq, _⟩⟩ := ok
  exact ⟨⟨a, b, ap, pb⟩, c, ⟨keysLt_weaken pq ap, pq, bq⟩, qc⟩

theorem leftRight (A B C : Tree) (p q k : Nat) (ordered : BST (node (node A q B) p C))
    (leftOK : Balanced (node A q B)) (rightOK : Balanced C)
    (taller : height B = k + 1) (inward : height A < height B) (hC : height C = k) :
    let t := node (node A q B) p C
    BST (doubleRotate t) ∧ Balanced (doubleRotate t) ∧ height (doubleRotate t) = k + 2 := by
  let t := node (node A q B) p C
  cases B with
  | leaf => simp [height] at taller
  | node B₁ r B₂ =>
    /- Open B. Its two children straddle r.

                 p
                / \
               q   C
              / \
             A   r
                / \
               B₁ B₂

       A < q       q < B₁ < r       r < B₂ < p       p < C -/
    spytial t

    /- Rotate left at q. B₁ must go on q’s right because q < B₁ < r.

                 p
                / \
               r   C
              / \
             q   B₂
            / \
           A   B₁
    -/
    spytial (rotateLeftChild t)

    have middleOK : BST (rotateLeftChild t) := by
      obtain ⟨leftBST, cBST, ⟨ap, qp, b₁p, rp, b₂p⟩, pc⟩ := ordered
      exact ⟨ordered_left leftBST, cBST, ⟨⟨ap, qp, b₁p⟩, rp, b₂p⟩, pc⟩
    obtain ⟨aOK, ⟨b₁OK, b₂OK, lr, rl⟩, _, ba⟩ := leftOK
    have hA : height A = k := by omega
    have tallest : max (height B₁) (height B₂) = k := by simpa [height] using taller
    have qOK : Balanced (node A q B₁) := ⟨aOK, b₁OK, by omega, by omega⟩
    have pOK : Balanced (node B₂ p C) := ⟨b₂OK, rightOK, by omega, by omega⟩
    have hq : height (node A q B₁) = k + 1 := by simp only [height]; omega
    have hp : height (node B₂ p C) = k + 1 := by simp only [height]; omega
    /- Rotate right at p. B₂ must go on p’s left because r < B₂ < p.

                 r
               /   \
              q     p
             / \   / \
            A  B₁  B₂  C

       A and C have height k here. The taller of B₁ and B₂ has height k. Since the subtree
       at r was balanced when its call returned, its other child is within one level of k.
       Both rebuilt nodes therefore have height k + 1. The last exercise tests exactly where
       we used that returned subtree’s balance. -/
    spytial (doubleRotate t) observing [height]

    refine ⟨ordered_right middleOK, ⟨qOK, pOK, by omega, by omega⟩, ?_⟩
    change max (height (node A q B₁)) (height (node B₂ p C)) + 1 = k + 2
    simp [hq, hp]

/-! ## 18.2.3.3 · Any Other Cases?

**1. Could the shorter subtree have height k − 2?** Take `k ≥ 2` in the left-right sketch
and suppose the insertion went into `B₁`. Before insertion, `B₁` had height `k − 1`.
A balanced `r` allowed `B₂` to be one level shorter, at `k − 2`. Grow `B₁` to `k` while
leaving `B₂` alone. There is now a gap of two **at r itself**. DCIC says “at most” here.
With a balanced starting tree, `k − 2` is the *least* height the unchanged sibling can have.

**2. What if we do both rotations at p anyway?** Use the same two shapes from §18.2.3.2.
Take `A`, `B₁`, and `C` of height `k`, and `B₂` of height `k − 2`.
Compare the two inspections in `premature_rotation`. Pink marks a gap of at least two.
[DCIC’s exercise](https://dcic-world.org/2025-08-27/sets-from-trees.html#%28part._.Any_.Other_.Cases_%29).
-/

theorem premature_rotation (A B₁ B₂ C : Tree) (p q r k : Nat) (hk : 2 ≤ k)
    (hA : height A = k) (h₁ : height B₁ = k) (h₂ : height B₂ = k - 2) (hC : height C = k) :
    let t := node (node A q (node B₁ r B₂)) p C
    factor (doubleRotate t) = 0 ∧ ¬ Balanced (doubleRotate t) := by
  -- Heights are natural numbers. With k ≥ 2, the integer factor sees the full gap.
  have short : ((k - 2 : Nat) : Int) = (k : Int) - 2 := by omega
  let t := node (node A q (node B₁ r B₂)) p C
  /- Read the factors on the same keys before and after the proposed repair.

             p (+2)                    r (0)
            / \                       /     \
           q   C                     q       p (−2)
          / \                       / \     / \
         A   r (+2)                A   B₁  B₂  C
            / \
           B₁ B₂
  -/
  spytial t observing [height, factor]
  -- The new root r has factor 0. Its right child p now pairs B₂ with C and has factor −2.
  spytial (doubleRotate t) observing [height, factor]
  constructor
  · change (height (node A q B₁) : Int) - height (node B₂ p C) = 0
    simp only [height, hA, h₁, h₂, hC]
    omega
  · intro ok
    have atP : Balanced (node B₂ p C) := ok.2.1
    have bound : height C ≤ height B₂ + 1 := atP.2.2.2
    omega

/-! **3. “Is there actually a bug in the above algorithm?”** Follow the return path. The call
at `r` checks the gap before its subtree can return to `q`, and `q` returns before `p`.
For `p` to receive the suspect shape unchanged, the call at `r` would have to return a
balanced node with children of heights `k` and `k − 2`. Here is the precise obstruction.
-/

theorem returnedSiblingBound (B₁ B₂ : Tree) (r k : Nat)
    (returned : Balanced (node B₁ r B₂)) (tall : height B₁ = k) : k - 1 ≤ height B₂ := by
  have fits : height B₁ ≤ height B₂ + 1 := returned.2.2.1
  omega

/-! Apply this bound at the two moments in the exercise. Before insertion the taller child had
height `k − 1`, so the bound allowed `k − 2`. A balanced return with one child of height `k`
requires the other to reach at least `k − 1`. The problematic shape must be repaired lower down.
-/

/-! ### A worked instance of the exercise

The chapter leaves the keys symbolic. For this Lean example choose **p = 8, q = 3, r = 6,
k = 2**. Initially `B₁` is the single key 5 and `B₂` is empty. Insert 4 on the left of 5.
The four inspections in `insertFour` show the balanced input, the raw insertion, and the two
possible choices of where to rotate. The trace in `insertFourReturns` then checks which choice
recursive insertion actually makes.
-/

theorem insertFour :
    let one := fun x => node leaf x leaf
    let atEight := fun inner => node (node (node (one 1) 2 leaf) 3 inner) 8 (node (one 9) 10 leaf)
    let before := node (one 5) 6 leaf
    let grown := node (node (one 4) 5 leaf) 6 leaf
    Balanced (atEight before) ∧ ¬ Balanced (doubleRotate (atEight grown)) ∧
      Balanced (atEight (rotateRight grown)) := by
  intro one atEight before grown
  -- Initially r = 6 has child heights 1 and 0. This whole tree is balanced.
  spytial (atEight before) observing [height, factor]
  -- Inserting 4 makes those heights 2 and 0, realizing k and k − 2.
  spytial (atEight grown) observing [height, factor]
  -- Try the chapter’s double rotation at p = 8. Find the −2 one level below the new root.
  spytial (doubleRotate (atEight grown)) observing [height, factor]
  -- Repair at r = 6 first. Its parent receives a subtree of height 2 rooted at 5.
  spytial (atEight (rotateRight grown)) observing [height, factor]
  simp [before, grown, atEight, one, doubleRotate, rotateLeftChild, rotateLeft, rotateRight,
    Balanced, height]

/-! ### Follow insertion on its way back up

Insert 4 into the same tree. When the child call returns, rebuild the current node and check
its balance. The blue outline marks the node being checked. Pink marks a gap of at least two.
Each picture shows the subtree belonging to that call.
-/

private def rebalance (t : Tree) : Tree :=
  match t with
  | leaf => leaf
  | node l x r =>
    if factor t > 1 then
      if factor l < 0 then doubleRotate t else rotateRight t
    else if factor t < -1 then
      if factor r > 0 then rotateLeft (node l x (rotateRight r)) else rotateLeft t
    else t

/-- Insert a key and collect the subtrees checked on return, in execution order. -/
def insert (x : Nat) : Tree → Tree × Array Tree
  | leaf => (node leaf x leaf, #[])
  | node l k r =>
    let ascend (left right : Tree) (checks : Array Tree) :=
      let current := spytial (node left k right) observing [height, factor]
      (rebalance current, checks.push current)
    if x < k then
      let (child, checks) := insert x l
      ascend child r checks
    else if k < x then
      let (child, checks) := insert x r
      ascend l child checks
    else (node l k r, #[])

private def insertFourRun : Tree × Array Tree :=
  let one := fun x => node leaf x leaf
  let atThree := node (node (one 1) 2 leaf) 3 (node (one 5) 6 leaf)
  insert 4 (node atThree 8 (node (one 9) 10 leaf))

def inorder : Tree → List Nat
  | leaf => []
  | node l key r => inorder l ++ key :: inorder r

/-! Step through `insertFourReturns`. Each inspection shows the current call just before
`rebalance`. The check at 6 and the next check at 3 show the two sides of the recursive
return. Watch which key becomes the right child of 3.
-/
theorem insertFourReturns : insertFourRun.2.size = 4 ∧ Balanced insertFourRun.1 ∧
    inorder insertFourRun.1 = [1, 2, 3, 4, 5, 6, 8, 9, 10] := by
  -- At 5, inserting 4 on the left gives factor +1.
  spytial insertFourRun.2[0] observing [height, factor]
  -- At r = 6, the child heights are 2 and 0. Factor +2 triggers a right rotation.
  spytial insertFourRun.2[1] observing [height, factor]
  -- q = 3 receives 5 as its right child, with 4 and 6 below it. Both children of 3 have height 2.
  spytial insertFourRun.2[2] observing [height, factor]
  -- By the time p = 8 is checked, its factor is +1. Insertion returns without rotating at p.
  spytial insertFourRun.2[3] observing [height, factor]
  refine ⟨rfl, ?_, rfl⟩
  repeat' first | apply And.intro | trivial

/-! One last check of the set represented by the schematic. Reading keys from left to right
gives the same list before and after the two rotations, for every choice of the four subtrees.
-/

theorem doubleRotate_inorder (A B₁ B₂ C : Tree) (p q r : Nat) :
    let t := node (node A q (node B₁ r B₂)) p C
    inorder (doubleRotate t) = inorder t := by
  simp [doubleRotate, rotateLeftChild, rotateLeft, rotateRight, inorder, List.append_assoc]

end DCICSetsFromTrees

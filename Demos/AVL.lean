import SpytialLean

open SpytialLean

/-!
# AVL repair: why one rotation fails and two succeed

This demo isolates AVL's recursive height-balance invariant. Keys are carried through the
rotations, but search ordering and insertion are separate concerns and are not assumed here.

Start with a left-right bend whose outer subtrees have height h and whose inner subtree has
height h + 1. All three subtrees are balanced; their keys, contents, and shapes are unknown.
A single right rotation leaves a height gap of two. Exposing just the inner subtree's root
reveals how a left rotation followed by a right rotation restores balance everywhere.

Follow the five `spytial` sites in `left_right_repair`. Heights are computed symbolically
from the current hypotheses. Green means `Balanced` has been proved; red means its negation
has been proved; neutral means neither has been established by the selector. An abstract
subtree is a whole unknown tree, not an empty leaf. Colors never stand in for the proof.
-/

namespace AVLDemo

inductive Tree where
  | leaf
  | node (left : Tree) (key : Nat) (right : Tree)

def height : Tree → Nat
  | .leaf => 0
  | .node l _ r => max (height l) (height r) + 1

/-- Every node is balanced, including all the nodes in its subtrees. -/
inductive Balanced : Tree → Prop where
  | leaf : Balanced .leaf
  | node {l r : Tree} {key : Nat} :
      Balanced l → Balanced r → height l ≤ height r + 1 → height r ≤ height l + 1 →
      Balanced (.node l key r)

theorem Balanced.children {l r : Tree} {key : Nat} (balanced : Balanced (.node l key r)) :
    Balanced l ∧ Balanced r ∧ height l ≤ height r + 1 ∧ height r ≤ height l + 1 := by
  cases balanced with
  | node bl br hl hr => exact ⟨bl, br, hl, hr⟩

def rotateRight : Tree → Tree
  | .node (.node a x b) z d => .node a x (.node b z d)
  | t => t

def rotateLeft : Tree → Tree
  | .node a x (.node b y c) => .node (.node a x b) y c
  | t => t

def rotateLeftRight : Tree → Tree
  | .node l z d => rotateRight (.node (rotateLeft l) z d)
  | t => t

-- One layout for every proof state. Only proved constructor fields become child edges.
-- The inspection adds `height` as an attribute and hides its scalar arithmetic scaffolding.
spytial_spec Tree [
  orientation left left below,
  orientation right right below,
  align ~(left + right).(left + right) - iden horizontal,
  attribute key,
  edgeStyle left noLabels,
  edgeStyle right noLabels,
  atomStyle Tree - lean (Balanced) - lean (fun t : Tree => ¬ Balanced t)
    (borderStyle "#64748b" 1) (fillStyle "#f8fafc"),
  atomStyle lean (Balanced) (borderStyle "#15803d" 2) (fillStyle "#f0fdf4"),
  atomStyle lean (fun t : Tree => ¬ Balanced t)
    (borderStyle "#b91c1c" 2) (fillStyle "#fef2f2")
]

/-- A left-right case defeats a single rotation; the double rotation is recursively balanced
and lowers the tree's height from h + 3 to h + 2. No subtree is instantiated concretely. -/
theorem left_right_repair (a inner d : Tree) (x z h : Nat)
    (ba : Balanced a) (bi : Balanced inner) (bd : Balanced d)
    (ha : height a = h) (hi : height inner = h + 1) (hd : height d = h) :
    let before := Tree.node (.node a x inner) z d
    ¬ Balanced (rotateRight before) ∧
      Balanced (rotateLeftRight before) ∧ height (rotateLeftRight before) = h + 2 := by
  let before := Tree.node (.node a x inner) z d
  change ¬ Balanced (rotateRight before) ∧
    Balanced (rotateLeftRight before) ∧ height (rotateLeftRight before) = h + 2

  have hleft : height (.node a x inner) = h + 2 := by simp only [height, ha, hi]; omega
  have hbefore : height before = h + 3 := by
    change max (height (.node a x inner)) (height d) + 1 = h + 3
    omega
  have badBefore : ¬ Balanced before := by
    intro balanced
    have bound := balanced.children.2.2.1
    change height (.node a x inner) ≤ height d + 1 at bound
    omega

  -- 1. The root has children of heights h + 2 and h. The taller child's inner subtree
  -- is still opaque, but its height h + 1 identifies the left-right bend.
  spytial before observing [height] with [.., attribute height, hideField Balanced, hideAtom Nat]

  let single := rotateRight before
  have hright : height (.node inner z d) = h + 2 := by simp only [height, hi, hd]; omega
  have hsingle : height single = h + 3 := by
    change max (height a) (height (.node inner z d)) + 1 = h + 3
    omega
  have badSingle : ¬ Balanced single := by
    intro balanced
    have bound := balanced.children.2.2.2
    change height (.node inner z d) ≤ height a + 1 at bound
    omega

  -- 2. The tempting repair fails: now the root's children have heights h and h + 2.
  -- This is a proof of failure for every permitted subtree, not one sampled counterexample.
  spytial single observing [height] with [.., attribute height, hideField Balanced, hideAtom Nat]
  refine ⟨badSingle, ?_⟩

  -- A height of h + 1 rules out a leaf. Reveal one constructor, not the entire subtree.
  cases inner with
  | leaf => simp [height] at hi
  | node b y c =>
      obtain ⟨bb, bc, hbc, hcb⟩ := bi.children
      have hmax : max (height b) (height c) = h := by simp only [height] at hi; omega
      -- Give the two still-unknown heights names. Neither is forced to equal h.
      generalize hb : height b = bh at hmax hbc hcb
      generalize hc : height c = ch at hmax hbc hcb
      have bUpper : bh ≤ h := by omega
      have cUpper : ch ≤ h := by omega
      have bLower : h ≤ bh + 1 := by omega
      have cLower : h ≤ ch + 1 := by omega

      -- 3. The bend is visible. b and c stay abstract; their heights lie within one of h.
      spytial before observing [height] with [
        .., attribute height, hideField Balanced, hideAtom Nat]

      -- Continue with the children's invariants; the old inner node is being replaced.
      clear bi
      let middle := Tree.node (rotateLeft (.node a x (.node b y c))) z d
      have hnewLeft : height (.node a x b) = h + 1 := by
        simp only [height, ha, hb]
        omega
      have hnewRight : height (.node c z d) = h + 1 := by
        simp only [height, hc, hd]
        omega
      have hmiddleLeft : height (rotateLeft (.node a x (.node b y c))) = h + 2 := by
        change max (height (.node a x b)) (height c) + 1 = h + 2
        omega
      have hmiddle : height middle = h + 3 := by
        change max (height (rotateLeft (.node a x (.node b y c)))) (height d) + 1 = h + 3
        omega
      have badMiddle : ¬ Balanced middle := by
        intro balanced
        have bound := balanced.children.2.2.1
        change height (rotateLeft (.node a x (.node b y c))) ≤ height d + 1 at bound
        omega

      -- 4. Rotating the child left straightens the bend but does not yet balance the root.
      -- Its height gap is still two; a right rotation at the root is the remaining step.
      spytial middle observing [height] with [
        .., attribute height, hideField Balanced, hideAtom Nat]

      let after := rotateRight middle
      have balancedLeft : Balanced (.node a x b) :=
        .node ba bb (by omega) (by omega)
      have balancedRight : Balanced (.node c z d) :=
        .node bc bd (by omega) (by omega)
      have balancedAfter : Balanced after := by
        exact .node balancedLeft balancedRight (by omega) (by omega)
      have hafter : height after = h + 2 := by
        change max (height (.node a x b)) (height (.node c z d)) + 1 = h + 2
        omega

      -- 5. The root's children both have height h + 1. The green root records the proved
      -- recursive invariant, including both new children and all four unknown subtrees.
      spytial after observing [height] with [.., attribute height, hideField Balanced, hideAtom Nat]
      exact ⟨balancedAfter, hafter⟩

end AVLDemo

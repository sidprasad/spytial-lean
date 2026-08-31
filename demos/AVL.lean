import SpytialLean

open SpytialLean

/-!
# Inspecting an AVL proof
-/

/-
Tier 1 and Tier 2 definitions used by the AVL development below.
-/

inductive Tree where
  | leaf
  | node (left : Tree) (key : Nat) (right : Tree)

spytial_spec Tree [
  orientation left - Tree->{t : Tree | @:t = leaf} left below,
  orientation right - Tree->{t : Tree | @:t = leaf} right below,
  align {x, y : Tree | @:x != leaf and @:y != leaf and (x.~(left + right) = y.~(left+right))} horizontal,
  attribute key,
  hideAtom {x : Tree | @:x = leaf}
]

-- And an example tree here.
#spytial (Tree.node (Tree.node Tree.leaf 1 Tree.leaf) 2 (Tree.node Tree.leaf 3 Tree.leaf))


def contains (x : Nat) : Tree → Bool
  | .leaf => false
  | .node l y r => x == y || contains x l || contains x r

def IsBST : Tree → Prop
  | .leaf => True
  | .node l x r =>
      (∀ z, contains z l = true → z < x) ∧
      (∀ z, contains z r = true → x < z) ∧
      IsBST l ∧ IsBST r

def bstLookup (x : Nat) : Tree → Bool
  | .leaf => false
  | .node l y r =>
      if x < y then bstLookup x l
      else if y < x then bstLookup x r
      else true

theorem bstLookup_eq_contains (x : Nat) (t : Tree) (h : IsBST t) :
    bstLookup x t = contains x t := by
  induction t with
  | leaf => rfl
  | node l y r ihl ihr =>
    obtain ⟨hl, hr, hbl, hbr⟩ := h
    simp only [bstLookup, contains]
    split
    · rename_i hxy
      rw [ihl hbl]
      have hright : contains x r = false := by
        cases hxr : contains x r with
        | false => rfl
        | true => have := hr x hxr; omega
      simp [hright, Nat.ne_of_lt hxy]
    · rename_i hnxy
      split
      · rename_i hyx
        rw [ihr hbr]
        have hleft : contains x l = false := by
          cases hxl : contains x l with
          | false => rfl
          | true => have := hl x hxl; omega
        have hne : x ≠ y := Nat.ne_of_gt hyx
        simp [hleft, hne]
      · rename_i hnyx
        have hxy : x = y := by omega
        subst x
        simp

/-
Tier 3: height-balanced (AVL) binary search tree.

Still the same `Tree` type from Tier 1. `Balanced` is a *second*, independent
invariant, orthogonal to `IsBST`. `IsAVL t := IsBST t ∧ Balanced t` refines
`IsBST` further, and — this is the point of the exercise — `bstLookup` and
its correctness proof from Tier 2 need *no change at all* to keep working
here: `avlInsert` only has to (re)establish `IsBST`, and Tier 2's
`bstLookup_eq_contains` already covers every `IsBST` tree, AVL or not.
-/

def height : Tree → Nat
  | .leaf => 0
  | .node l _ r => 1 + max (height l) (height r)

/-- Every node's two children differ in height by at most one — stated with
    two `≤`'s rather than a subtraction, since `Nat` subtraction truncates
    at zero and `height l - height r ≤ 1` would silently be true whenever
    `l` is merely *shorter*, not just close in height. -/
def Balanced : Tree → Prop
  | .leaf => True
  | .node l _ r =>
      height l ≤ height r + 1 ∧ height r ≤ height l + 1 ∧
      Balanced l ∧ Balanced r

def IsAVL (t : Tree) : Prop := IsBST t ∧ Balanced t

/-- The refinement chain, made literal: every AVL tree's underlying data
    *is* a BST (same value, extra proof obligation discharged), and every
    BST's underlying data *is* a plain tree. -/
def BSTree := {t : Tree // IsBST t}
def AVLTree := {t : Tree // IsAVL t}

def AVLTree.toBST (t : AVLTree) : BSTree := ⟨t.1, t.2.1⟩

-- ---------------------------------------------------------------------
-- Rotations. Local, constant-size tree surgery; no invariant assumed.
-- ---------------------------------------------------------------------

def rotateRight (t : Tree) : Tree := by
  spytial t                            -- At entry
  exact match t with
    | before@(.node (.node ll lx lr) x r) => by
        spytial before                 -- Before rotation
        let after := Tree.node ll lx (.node lr x r)
        spytial after                  -- After rotation
        exact after
    | other => other

def rotateLeft (t : Tree) : Tree := by
  spytial t                            -- At entry
  exact match t with
    | before@(.node l x (.node rl rx rr)) => by
        spytial before                 -- Before rotation
        let after := Tree.node (.node l x rl) rx rr
        spytial after                  -- After rotation
        exact after
    | other => other

/-- Re-balance a node whose children are each already balanced but may
    differ from each other in height by up to 2 (the amount a single
    insertion can produce). Standard four-case (LL/LR/RL/RR) dispatch. -/
def balance (t : Tree) : Tree := by
  spytial t observing [height]         -- At entry, before any shape is known
  exact match t with
  | .leaf => .leaf
  | before@(.node l x r) =>
    if hLeft : height l > height r + 1 then
      match l with
      | .node ll lx lr =>
        if hInner : height lr > height ll then by
          -- LR: expose the inner subtree so both rotations can compute symbolically.
          cases lr with
          | leaf => simp [height] at hInner
          | node a y b =>
            let left := Tree.node ll lx (.node a y b)
            let before := Tree.node left x r
            spytial before observing [height]  -- The left-right bend
            let middle := Tree.node (rotateLeft left) x r
            spytial middle observing [height]  -- After rotating the child left
            let after := rotateRight middle
            spytial after observing [height]   -- After rotating the parent right
            exact after
        else by
          -- LL: rotate the parent right; lr moves across to x's left.
          let before := Tree.node (.node ll lx lr) x r
          spytial before observing [height]
          let after := rotateRight before
          spytial after observing [height]
          exact after
      | .leaf => before
    else if hRight : height r > height l + 1 then
      match r with
      | .node rl rx rr =>
        if hInner : height rl > height rr then by
          -- RL: the mirror image, with a right rotation of the child first.
          cases rl with
          | leaf => simp [height] at hInner
          | node a y b =>
            let right := Tree.node (.node a y b) rx rr
            let before := Tree.node l x right
            spytial before observing [height]  -- The right-left bend
            let middle := Tree.node l x (rotateRight right)
            spytial middle observing [height]  -- After rotating the child right
            let after := rotateLeft middle
            spytial after observing [height]   -- After rotating the parent left
            exact after
        else by
          -- RR: one left rotation, moving rl across to x's right.
          let before := Tree.node l x (.node rl rx rr)
          spytial before observing [height]
          let after := rotateLeft before
          spytial after observing [height]
          exact after
      | .leaf => before
    else by
      -- Neither side exceeds the height threshold: the tree is returned unchanged.
      spytial before observing [height]
      exact before

def avlInsert (x : Nat) : Tree → Tree
  | .leaf => .node .leaf x .leaf
  | .node l y r =>
      if x < y then balance (.node (avlInsert x l) y r)
      else if y < x then balance (.node l y (avlInsert x r))
      else .node l y r

-- ---------------------------------------------------------------------
-- Rotation is just tree surgery: it never adds or removes a value.
-- ---------------------------------------------------------------------

theorem contains_rotateRight (z : Nat) (t : Tree) :
    contains z (rotateRight t) = contains z t := by
  match t with
  | .leaf => rfl
  | .node .leaf _ _ => rfl
  | .node (.node ll lx lr) x r =>
    show contains z (Tree.node ll lx (Tree.node lr x r)) =
      contains z (Tree.node (Tree.node ll lx lr) x r)
    simp only [contains]
    ac_rfl

theorem contains_rotateLeft (z : Nat) (t : Tree) :
    contains z (rotateLeft t) = contains z t := by
  match t with
  | .leaf => rfl
  | .node _ _ .leaf => rfl
  | .node l x (.node rl rx rr) =>
    show contains z (Tree.node (Tree.node l x rl) rx rr) =
      contains z (Tree.node l x (Tree.node rl rx rr))
    simp only [contains]
    ac_rfl

theorem contains_balance (z : Nat) (t : Tree) :
    contains z (balance t) = contains z t := by
  cases t with
  | leaf => rfl
  | node l x r =>
    simp only [balance]
    split
    · cases l with
      | leaf => rfl
      | node ll lx lr =>
        dsimp only
        split
        · rename_i hInner
          cases lr with
          | leaf => simp [height] at hInner
          | node a y b =>
            dsimp only
            rw [contains_rotateRight]
            simp [contains, contains_rotateLeft]
        · exact contains_rotateRight z _
    · split
      · cases r with
        | leaf => rfl
        | node rl rx rr =>
          dsimp only
          split
          · rename_i hInner
            cases rl with
            | leaf => simp [height] at hInner
            | node a y b =>
              dsimp only
              rw [contains_rotateLeft]
              simp [contains, contains_rotateRight]
          · exact contains_rotateLeft z _
      · rfl

-- ---------------------------------------------------------------------
-- Rotation also preserves BST-ness (given as a hypothesis on the specific
-- shape rotation fires on — a leaf can't rotate). This is where the
-- interesting reasoning lives: the pivot's old bound (`lx < x`) has to be
-- *re-derived*, not assumed, since it wasn't stated directly by `IsBST`.
-- ---------------------------------------------------------------------

theorem IsBST_rotateRight (x : Nat) (ll : Tree) (lx : Nat) (lr r : Tree)
    (h : IsBST (.node (.node ll lx lr) x r)) :
    IsBST (rotateRight (.node (.node ll lx lr) x r)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h3a, h3b, h3c, h3d⟩ := h3
  have hlxx : lx < x := h1 lx (by simp [contains])
  show IsBST (.node ll lx (.node lr x r))
  refine ⟨h3a, ?_, h3c, ?_, h2, h3d, h4⟩
  · intro z hz
    rw [contains] at hz
    rcases Bool.or_eq_true_iff.mp hz with hz | hz
    · rcases Bool.or_eq_true_iff.mp hz with hz | hz
      · have : z = x := by simpa using hz
        omega
      · exact h3b z hz
    · have := h2 z hz
      omega
  · intro z hz
    have hzLeft : contains z (.node ll lx lr) = true := by simp [contains, hz]
    -- Why may lr move from lx's right to x's left? Inspect the old left subtree with an
    -- arbitrary member z of lr. The dotted edges show membership; the blue bounds give
    -- lx < z < x. `fyi` instantiates the existing bounds h3b and h1 for the inspection;
    -- the proof still has to apply h1 below. None of the subtrees needs to be concrete.
    -- Keep keys as vertices here: unlike the usual tree layout, the ordering is the point.
    spytial (Tree.node ll lx lr) observing [height] with [.., hideField IsBST]
    exact h1 z hzLeft

theorem IsBST_rotateLeft (x : Nat) (l rl : Tree) (rx : Nat) (rr : Tree)
    (h : IsBST (.node l x (.node rl rx rr))) :
    IsBST (rotateLeft (.node l x (.node rl rx rr))) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h4a, h4b, h4c, h4d⟩ := h4
  have hxrx : x < rx := h2 rx (by simp [contains])
  show IsBST (.node (.node l x rl) rx rr)
  refine ⟨?_, h4b, ⟨h1, ?_, h3, h4c⟩, h4d⟩
  · intro z hz
    rw [contains] at hz
    rcases Bool.or_eq_true_iff.mp hz with hz | hz
    · rcases Bool.or_eq_true_iff.mp hz with hz | hz
      · have : z = x := by simpa using hz
        omega
      · have := h1 z hz
        omega
    · exact h4a z hz
  · intro z hz
    exact h2 z (by simp [contains, hz])

-- ---------------------------------------------------------------------
-- `balance` preserves BST-ness. The LL/RR cases are single rotations, so
-- they're immediate from the lemmas above. LR/RL are a rotation of a
-- rotation: the inner `rotateLeft`/`rotateRight` first has to be shown to
-- land back in `IsBST`, then the outer one applies to *that*.
-- ---------------------------------------------------------------------

theorem IsBST_balance (t : Tree) (h : IsBST t) : IsBST (balance t) := by
  cases t with
  | leaf => exact h
  | node l x r =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    -- `simp only [balance]` (an equation lemma, not `unfold`) is what makes the
    -- rewrite land cleanly on the already-known `.node l x r` shape; a bare
    -- `unfold` here leaves a redex that later `split`s can't safely case on,
    -- producing bogus impossible-looking goals. Likewise `dsimp only` right
    -- after each `cases` collapses the *next* embedded `match` before `split`
    -- has to look at it.
    simp only [balance]
    split
    · cases l with
      | leaf => dsimp only; exact ⟨h1, h2, h3, h4⟩
      | node ll lx lr =>
        obtain ⟨h3a, h3b, h3c, h3d⟩ := h3
        dsimp only
        split
        · -- Why rotate the child before the parent? The left subtree is too tall, but lr is
          -- taller than ll. Inspect at the LR decision while both still have symbolic names,
          -- before exposing lr's shape and constructing the intermediate BST.
          spytial lr observing [height] with [.., hideField IsBST]
          cases lr with
          | leaf => exfalso; simp only [height] at *; omega
          | node rl' rx' rr' =>
            have hMid :
                IsBST (.node (rotateLeft (.node ll lx (.node rl' rx' rr'))) x r) := by
              refine ⟨?_, h2, IsBST_rotateLeft lx ll rl' rx' rr'
                ⟨h3a, h3b, h3c, h3d⟩, h4⟩
              intro z hz
              rw [contains_rotateLeft] at hz
              exact h1 z hz
            exact IsBST_rotateRight x (.node ll lx rl') rx' rr' r hMid
        · exact IsBST_rotateRight x ll lx lr r
            ⟨h1, h2, ⟨h3a, h3b, h3c, h3d⟩, h4⟩
    · split
      · cases r with
        | leaf => dsimp only; exact ⟨h1, h2, h3, h4⟩
        | node rl rx rr =>
          obtain ⟨h4a, h4b, h4c, h4d⟩ := h4
          dsimp only
          cases rl with
          | leaf =>
            split
            · exfalso; simp only [height] at *; omega
            · exact IsBST_rotateLeft x l .leaf rx rr
                ⟨h1, h2, h3, ⟨h4a, h4b, h4c, h4d⟩⟩
          | node ll' lx' lr' =>
            split
            · have hMid :
                  IsBST (.node l x (rotateRight (.node (.node ll' lx' lr') rx rr))) := by
                refine ⟨h1, ?_, h3, IsBST_rotateRight rx ll' lx' lr' rr
                  ⟨h4a, h4b, h4c, h4d⟩⟩
                intro z hz
                rw [contains_rotateRight] at hz
                exact h2 z hz
              exact IsBST_rotateLeft x l ll' lx' (.node lr' rx rr) hMid
            · exact IsBST_rotateLeft x l (.node ll' lx' lr') rx rr
                ⟨h1, h2, h3, ⟨h4a, h4b, h4c, h4d⟩⟩
      · exact ⟨h1, h2, h3, h4⟩

-- ---------------------------------------------------------------------
-- avlInsert only ever adds `x` to the membership set (same statement,
-- same proof shape as Tier 2's `contains_bstInsert` — `balance` is
-- membership-preserving, so it just slots in via `contains_balance`).
-- ---------------------------------------------------------------------

theorem contains_avlInsert (x z : Nat) (t : Tree) :
    contains z (avlInsert x t) = (z == x || contains z t) := by
  induction t with
  | leaf => simp [avlInsert, contains]
  | node l y r ihl ihr =>
    unfold avlInsert
    split
    · rw [contains_balance, contains, ihl, contains]
      ac_rfl
    · split
      · rw [contains_balance, contains, ihr, contains]
        ac_rfl
      · rename_i hxy hyx
        have hxeq : x = y := by omega
        subst hxeq
        rw [contains]
        show ((z == x || contains z l) || contains z r) =
          (z == x || ((z == x || contains z l) || contains z r))
        ac_rfl

-- ---------------------------------------------------------------------
-- The Tier-2 theorem again: `avlInsert` preserves `IsBST`. Identical
-- structure to `IsBST_bstInsert`, with the recursive call now wrapped in
-- `balance` and discharged via `IsBST_balance`.
-- ---------------------------------------------------------------------

theorem IsBST_avlInsert (x : Nat) (t : Tree) (h : IsBST t) : IsBST (avlInsert x t) := by
  induction t with
  | leaf => simp [avlInsert, IsBST, contains]
  | node l y r ihl ihr =>
    obtain ⟨hl, hr, hbl, hbr⟩ := h
    unfold avlInsert
    split
    · apply IsBST_balance
      refine ⟨?_, hr, ihl hbl, hbr⟩
      intro z hz
      rw [contains_avlInsert] at hz
      rcases Bool.or_eq_true_iff.mp hz with h1 | h1
      · have : z = x := by simpa using h1
        omega
      · exact hl z h1
    · split
      · apply IsBST_balance
        refine ⟨hl, ?_, hbl, ihr hbr⟩
        intro z hz
        rw [contains_avlInsert] at hz
        rcases Bool.or_eq_true_iff.mp hz with h1 | h1
        · have : z = x := by simpa using h1
          omega
        · exact hr z h1
      · exact ⟨hl, hr, hbl, hbr⟩

-- ---------------------------------------------------------------------
-- The payoff, made explicit: inserting into an AVL tree and then looking
-- up with the *efficient* `bstLookup` is provably correct — and this
-- required **zero** new lookup-specific reasoning. `IsBST_avlInsert`
-- re-establishes the one hypothesis `bstLookup_eq_contains` (Tier 2)
-- needs, and Tier 2's proof is reused completely unchanged.
-- ---------------------------------------------------------------------

theorem avlInsert_bstLookup_eq_contains (x y : Nat) (t : Tree) (h : IsBST t) :
    bstLookup y (avlInsert x t) = contains y (avlInsert x t) :=
  bstLookup_eq_contains y (avlInsert x t) (IsBST_avlInsert x t h)

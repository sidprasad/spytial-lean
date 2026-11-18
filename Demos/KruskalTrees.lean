import SpytialLean

/-!
# Kruskal's tree theorem, after Minchao Wu

Minchao Wu's CMU thesis formalizes Kruskal's tree theorem in Lean 2, following
Nash-Williams's minimal bad sequence proof.
[Thesis PDF](https://www.andrew.cmu.edu/user/avigad/Students/wu_thesis.pdf)

This demo ports the parts of the thesis that are about trees. It uses the thesis's encoding
(§2.2.2), its homeomorphic embedding (Definition 2.6), Theorems 2.1 to 2.3, and the step that
applies the minimal bad sequence argument to trees (Theorems 3.24 and 3.25). It does not port
Dickson's lemma, Higman's lemma, or the construction of the minimal bad sequence. Those are
about sequences and sets, not about the shape of a tree.

Place the cursor on each `#spytial` command and on each `spytial` line inside a proof.
-/

namespace KruskalTrees

open SpytialLean

/-! ## Finite trees (§2.2.2)

The thesis writes a tree as a node with `n` children, given as a function out of `Fin n`.
A node with `Fin 0` has no children. The tree carries no labels, so every node is drawn alike.
-/

inductive FTree where
  | cons : {n : Nat} → (Fin n → FTree) → FTree

-- Equal subtrees are still different positions in the tree, so draw each one separately.
instance : SpytialIdentity FTree := .asWritten

namespace FTree

/-- The tree with no children (the thesis's `node`). -/
def node : FTree := cons (n := 0) Fin.elim0

/-- Build a tree from a list of children. Only for writing examples. -/
def of (ts : List FTree) : FTree := cons fun i : Fin ts.length => ts[i]

/-- Summation over a list (the thesis's `Suml`). -/
def sumOver {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: as => f a + sumOver f as

/-- Definition 2.7: one for the root plus the sizes of all branches. -/
def size : FTree → Nat
  | @cons n ts => sumOver (fun i => size (ts i)) (List.finRange n) + 1

end FTree

open FTree

def cherry : FTree := of [node, node]
def path1 : FTree := of [node]
def path2 : FTree := of [path1]
def path3 : FTree := of [path2]
def star3 : FTree := of [node, node, node]

-- The child relation `cons_1` has three columns: parent, index, child. Hide the index.
spytial_ops treeView : FTree [
  hideAtom Nat + Fin,
  hideField n,
  edgeStyle cons_1 noLabels,
  orientation cons_1 below,
  align let kid = {p, c : FTree | some p.cons_1.c} | ~kid.kid - iden horizontal
]

-- Each node shows the size of the subtree below it.
#spytial of [cherry, path2, node] observing [size] with [..treeView, attribute size]

/-! ## Homeomorphic embedding (Definition 2.6)

`s` embeds in `t` if (E1) `s` embeds in some branch of `t`, or (E2) an injective map sends
each branch of `s` to a branch of `t` that it embeds in. The thesis defines this by recursion.
We use an inductive predicate with one constructor per case, so proofs can use `cases`.
-/

inductive Embeds : FTree → FTree → Prop
  /-- (E1) Embed in branch `j`. -/
  | left {s : FTree} {m : Nat} {us : Fin m → FTree} (j : Fin m) :
      Embeds s (us j) → Embeds s (cons us)
  /-- (E2) Match the branches injectively. -/
  | right {n m : Nat} {ts : Fin n → FTree} {us : Fin m → FTree} (f : Fin n → Fin m) :
      Function.Injective f → (∀ i, Embeds (ts i) (us (f i))) → Embeds (cons ts) (cons us)

/-- `t` is a branch of `T`. The thesis's `branches T` also records the index. -/
inductive IsBranch : FTree → FTree → Prop
  | mk {m : Nat} (us : Fin m → FTree) (k : Fin m) : IsBranch (us k) (cons us)

/-! To draw embeddings between concrete trees, we use a brute-force search, `embeds?`.
It follows E1 and E2. It is only used for drawing and is not proved equal to `Embeds`. -/

namespace FTree

/-- Can each index in `is` get its own `j`, not yet in `used`, with `ok i j`? -/
def matchAll {n m : Nat} (ok : Fin n → Fin m → Bool) : List (Fin n) → List (Fin m) → Bool
  | [], _ => true
  | i :: is, used =>
    (List.finRange m).any fun j => !used.contains j && ok i j && matchAll ok is (j :: used)

def embeds? : FTree → FTree → Bool
  | s, @cons m us =>
    (List.finRange m).any (fun j => embeds? s (us j)) ||
    match s with
    | @cons n ts => matchAll (fun i j => embeds? (ts i) (us j)) (List.finRange n) []

end FTree

/-- Two trees to compare. -/
structure Pair where
  small : FTree
  big : FTree

-- Dashed arrows go from `small` and its branches to the branches of `big`.
-- An arrow from the root of `small` is case E1. Arrows from its branches are candidates for E2.
spytial_ops pairView : Pair [
  hideAtom Nat + Fin + Pair,
  hideField n,
  edgeStyle cons_1 noLabels,
  orientation cons_1 below,
  align let kid = {p, c : FTree | some p.cons_1.c} | ~kid.kid - iden horizontal,
  orientation inspectedRoot.small -> inspectedRoot.big right,
  align inspectedRoot.small -> inspectedRoot.big horizontal,
  inferredEdge emb lean (fun a b : FTree => embeds? a b) &
    ((inspectedRoot.small + univ.(inspectedRoot.small.cons_1)) -> univ.(inspectedRoot.big.cons_1))
    (lineStyle "#2563eb" dashed)
]

-- Each branch of the cherry embeds in the only branch of the path. Why is that not enough?
#spytial Pair.mk cherry (of [path2]) with [..pairView]

-- Add one more branch to the big tree. Can you now choose different targets?
#spytial Pair.mk cherry (of [path2, node]) with [..pairView]

/-! ## Theorems 2.1 to 2.3 -/

/-- The thesis's `node_embeds`: the tree with no children embeds in every tree. -/
theorem node_embeds : ∀ t, Embeds node t
  | cons _ => .right Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)

/-- Theorem 2.1, reflexivity: use the identity on branches. -/
theorem Embeds.refl : ∀ t, Embeds t t
  | cons ts => .right id (fun _ _ h => h) fun i => Embeds.refl (ts i)

/-- Theorem 2.1, transitivity. Induction on the second embedding, as in the thesis. -/
theorem Embeds.trans {s t u : FTree} (h1 : Embeds s t) (h2 : Embeds t u) : Embeds s u := by
  induction h2 generalizing s with
  | left j _ ih => exact .left j (ih h1)
  | right f inj _ ih =>
    cases h1 with
    | left j h => exact .left (f j) (ih j h)
    | right g injg hs => exact .right (f ∘ g) (inj.comp injg) fun i => ih (g i) (hs i)

/-- Theorem 2.2: a branch embeds in its tree. -/
theorem Embeds.of_branch {t T : FTree} (h : IsBranch t T) : Embeds t T := by
  cases h with
  | mk us k => exact .left k (Embeds.refl _)

theorem le_sumOver {α : Type} (f : α → Nat) : ∀ {l : List α} {a : α}, a ∈ l → f a ≤ sumOver f l
  | _ :: _, _, .head _ => Nat.le_add_right _ _
  | b :: _, _, .tail _ h => Nat.le_trans (le_sumOver f h) (Nat.le_add_left _ (f b))

/-- Theorem 2.3: a branch is smaller than its tree. -/
theorem size_lt_of_branch {t T : FTree} (h : IsBranch t T) : size t < size T := by
  cases h with
  | mk us k =>
    simp only [size]
    exact Nat.lt_succ_of_le (le_sumOver (fun i => size (us i)) (List.mem_finRange k))

/-! ## Bad sequences (Definition 2.2)

A sequence of trees is good if some earlier tree embeds in some later one. It is bad otherwise.
Kruskal's theorem says that no infinite sequence of trees is bad.

Below is the start of a bad sequence. Dashed arrows show every embedding between two of its
trees. Every arrow points back to an earlier tree. Can you add a sixth tree and keep it bad?
-/

/-- A finite stretch of a sequence of trees, in order. -/
inductive Stretch where
  | stop
  | next (tree : FTree) (later : Stretch)

def Stretch.ofList : List FTree → Stretch
  | [] => .stop
  | t :: ts => .next t (Stretch.ofList ts)

spytial_ops stretchView : Stretch [
  hideAtom Nat + Fin + Stretch,
  hideField n,
  edgeStyle cons_1 noLabels,
  orientation cons_1 below,
  align let kid = {p, c : FTree | some p.cons_1.c} | ~kid.kid - iden horizontal,
  orientation ~tree.later.tree right,
  align ~tree.later.tree horizontal,
  group let kid = {p, c : FTree | some p.cons_1.c} | univ.tree <: *kid tree,
  inferredEdge emb lean (fun a b : FTree => embeds? a b) & (univ.tree -> univ.tree) - iden
    (lineStyle "#2563eb" dashed)
]

#spytial Stretch.ofList [star3, path3, cherry, path2, node] with [..stretchView]

-- No. The last tree is `node`, and `node_embeds` sends it into any sixth tree.
example (t : FTree) : Embeds node t := node_embeds t

/-! ## Applying the minimal bad sequence argument to trees (§3.3.2)

Suppose `mbs` is a minimal bad sequence of trees. The proof builds a new sequence `g` from
branches. Each `g n` is a branch of the tree `mbs (h n)`. The new sequence starts with a
tree smaller than `mbs (h 0)` (Theorem 3.24). An embedding from an earlier tree `mbs i` into
`g j` extends to `mbs (h j)` (Theorem 3.25). Together these contradict minimality.

The thesis builds `g` and `h` from a bad sequence of branches. Here they are section
variables with the one property both theorems use.
-/

section MinimalBadSequence

variable (mbs g : Nat → FTree) (h : Nat → Nat) (hg : ∀ n, IsBranch (g n) (mbs (h n)))

include hg in
/-- Theorem 3.24: the new sequence starts with a smaller tree. -/
theorem size_g_lt (n : Nat) : size (g n) < size (mbs (h n)) := by
  have branch := hg n
  have smaller := size_lt_of_branch branch
  -- Both sizes stay unknown. The diagram shows only how they compare.
  spytial (g n) observing [size, IsBranch] with [attribute size] titled "A branch and its tree"
  exact smaller

include hg in
/-- Theorem 3.25: an embedding into a branch extends to the whole tree. -/
theorem embeds_mbs_of_embeds_g (i j : Nat) (H1 : Embeds (mbs i) (g j)) :
    Embeds (mbs i) (mbs (h j)) := by
  have branch := hg j
  spytial (mbs i) observing [Embeds, IsBranch] with [
    edgeStyle Embeds (lineStyle "#2563eb" dashed)] titled "What we are given"
  have up := Embeds.of_branch branch
  have goal := H1.trans up
  spytial (mbs i) observing [Embeds, IsBranch] with [
    edgeStyle Embeds (lineStyle "#2563eb" dashed)] titled "After Theorem 2.2 and transitivity"
  exact goal

end MinimalBadSequence

end KruskalTrees

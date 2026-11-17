import SpytialLean

/-!
# Would you try to prove this rotation balanced?

Insertion has made the left child two levels too tall. A right rotation preserves
the order of every key. Should we keep that code and start proving balance?

Start at the first `spytial` in `rebalanceLeft`. No one has supplied a tree to run.
The keys and the height of the untouched right subtree are unknown. Yet Lean knows how its height compares to two others. Inspect the *proposed
return value* with those facts in scope. Its two child heights decide whether the code
is worth keeping. The next inspection shows which subtree can supply a pivot.

This experiment specializes Alexander Gillon’s verified map to natural-number keys
and retains balance, cached heights and the in-order key sequence. The trial rotation
is our question. Gillon’s implementation takes the successful branch.
-/

namespace GillonAVL
open SpytialLean

inductive Tree where
  | leaf
  | node (cache : Nat) (left : Tree) (key : Nat) (right : Tree)

open Tree

def height : Tree → Nat
  | leaf => 0
  | node _ l _ r => max (height l) (height r) + 1

def cachedHeight : Tree → Nat
  | leaf => 0
  | node h _ _ _ => h

def join (l : Tree) (k : Nat) (r : Tree) : Tree :=
  node (max (cachedHeight l) (cachedHeight r) + 1) l k r

def keys : Tree → List Nat
  | leaf => []
  | node _ l k r => keys l ++ k :: keys r

def Valid : Tree → Prop
  | leaf => True
  | node h l _ r => Valid l ∧ Valid r ∧ h = max (height l) (height r) + 1 ∧
      height l ≤ height r + 1 ∧ height r ≤ height l + 1

theorem Valid.cache {t : Tree} (ok : Valid t) : cachedHeight t = height t := by
  cases t with
  | leaf => rfl
  | node _ _ _ _ => exact ok.2.2.1

theorem Valid.join {l r : Tree} (k : Nat) (hl : Valid l) (hr : Valid r)
    (lr : height l ≤ height r + 1) (rl : height r ≤ height l + 1) : Valid (join l k r) :=
  ⟨hl, hr, by rw [hl.cache, hr.cache], lr, rl⟩

structure Repair (expectedKeys : List Nat) where
  tree : Tree
  valid : Valid tree
  keepsKeys : keys tree = expectedKeys

spytial_spec Tree [
  orientation inspectedRoot.*(left + right) <: (left + right) below,
  -- All empty children share one leaf, which can occur on both sides of a parent.
  orientation inspectedRoot.*(left + right) <: left.*(left + right) :> (Tree - lean (fun t : Tree => t matches .leaf)) left,
  orientation inspectedRoot.*(left + right) <: right.*(left + right) :> (Tree - lean (fun t : Tree => t matches .leaf)) right,
  align let tree = inspectedRoot.*(left + right) |
    (tree <: lean (fun a b : Tree => height a = height b) :> tree) - iden horizontal,
  attribute key,
  hideField cache,
  hideAtom univ - inspectedRoot.*(left + right),
]

/-- The two children are valid. Inserting on the left has opened a height gap of two. -/
def rebalanceLeft (left : Tree) (z : Nat) (d : Tree) (hl : Valid left) (hd : Valid d)
    (gap : height left = height d + 2) : Repair (keys left ++ z :: keys d) :=
  match left with
  | leaf => by simp [height] at gap
  | node cache a x inner =>
    if heavy : height inner > height a then
      have innerLevel : height inner = height d + 1 := by simp [height] at gap; omega
      have outerLevel : height a = height d := by
        have := hl.2.2.2.2
        omega
      have pivotExists : inner ≠ leaf := by
        -- Try the single rotation before writing its balance proof. Read the two
        -- edges out of x. If d has height h, the children have heights h and h + 2.
        -- The key sequence survives. This candidate fails for every input in the branch.
        spytial (join a x (join inner z d)) observing [height] with [.., attribute height]
        -- Follow x’s right edge. inner lies between x and z in the key order and
        -- its height is h + 1. We can open it for a pivot and leave a and d opaque.
        spytial (join (node cache a x inner) z d) observing [height] with [.., attribute height]
        intro empty
        simp [empty, height] at heavy
      match h : inner with
      | leaf => False.elim (pivotExists rfl)
      | node _ b y c => by
        subst inner
        obtain ⟨va, ⟨vb, vc, _, bc, cb⟩, _⟩ := hl
        simp only [height] at innerLevel
        -- b and c are still opaque. Each is at most as tall as d and at most one shorter.
        have bUpper : height b ≤ height d := by omega
        have cUpper : height c ≤ height d := by omega
        let newLeft := join a x b
        let newRight := join c z d
        -- Each new child has a fringe of height h and another of height at most h.
        -- Inspect their computed heights before either equality is a named lemma.
        let rebuilt : Tree := spytial (join newLeft y newRight) observing [height] with [.., attribute height]
        have leftOK : Valid newLeft := va.join x vb (by omega) (by omega)
        have rightOK : Valid newRight := vc.join z hd (by omega) (by omega)
        refine ⟨rebuilt, ?_, by simp [rebuilt, newLeft, newRight, keys, join, List.append_assoc]⟩
        have leftHeight : height newLeft = height d + 1 := by
          simp only [newLeft, join, height]; omega
        have rightHeight : height newRight = height d + 1 := by
          simp only [newRight, join, height]; omega
        -- The equal heights of y’s two children are now proved. The boxes for b and c still
        -- have no children on display. We can finish without splitting either tree.
        spytial rebuilt observing [height] with [.., attribute height]
        exact leftOK.join y rightOK (by omega) (by omega)
    else by
      obtain ⟨va, vi, _, ai, ia⟩ := hl
      simp only [height] at gap
      let newRight := join inner z d
      have rightOK : Valid newRight := vi.join z hd (by omega) (by omega)
      have rightHeight : height newRight = max (height inner) (height d) + 1 := rfl
      -- Try the same single rotation with the other branch’s hypotheses. This time
      -- x’s children fit within one level, so the validity proof can go through.
      refine ⟨spytial (join a x newRight) observing [height] with [.., attribute height],
        va.join x rightOK (by omega) (by omega), ?_⟩
      simp [newRight, join, keys, List.append_assoc]

/-- Resume insertion at its parent. The recursive call supplies a valid subtree
whose height either stayed the same or grew by one. -/
def insertLeftSubtree (oldLeft left : Tree) (z : Nat) (right : Tree)
    (oldOK : Valid (join oldLeft z right)) (newOK : Valid left)
    (growth : height left = height oldLeft ∨ height left = height oldLeft + 1) :
    Repair (keys left ++ z :: keys right) := by
  obtain ⟨_, rightOK, _, oldLR, oldRL⟩ := oldOK
  if fits : height left ≤ height right + 1 then
    exact ⟨join left z right, newOK.join z rightOK fits (by omega), rfl⟩
  else
    have gap : height left = height right + 2 := by omega
    -- The two heights expose the overflow. The children of left are still opaque,
    -- so this inspection alone cannot choose between a single and a double rotation.
    spytial (join left z right) observing [height] with [.., attribute height]
    exact rebalanceLeft left z right newOK rightOK gap


/-- Check the diagnosis from the first inspection. The two hypotheses are exactly
`outerLevel` and `innerLevel` proved in the branch above. -/
theorem singleRotation_innerHeavy (a inner d : Tree) (x z : Nat)
    (outerLevel : height a = height d) (innerLevel : height inner = height d + 1) :
    keys (join a x (join inner z d)) = keys (join (join a x inner) z d) ∧
      ¬ Valid (join a x (join inner z d)) := by
  constructor
  · simp [join, keys, List.append_assoc]
  · intro ok
    have wouldFit := ok.2.2.2.2
    change height (join inner z d) ≤ height a + 1 at wouldFit
    simp only [join, height] at wouldFit
    omega

end GillonAVL

import Demos.Showcase

/-!
# Red-black deletion: can we just recolor the sibling?

Deletion has left the subtree under key 20's left edge one black node short.
Its sibling (40) is black and the sibling's inner child (30) is red. The four
fringe subtrees `x`, `a`, `b`, and `c` have unknown contents. Each is a valid
black-rooted subtree of black height `h`.

Follow the four `spytial` lines below. The first pair evaluates a function on
the partially known tree. The second pair inspects a proof of the repair.
Keys identify the three pivots. Each neutral box stands for a whole opaque
subtree. On the children, `bh` gives the number of black nodes on a path to a
leaf, counting the subtree's root when it is black.
-/

open SpytialLean

namespace RedBlackDeletion

open RBNode

def rootColor : RBNode → Color
  | .nil => .black
  | .node color _ _ _ => color

/-- Count along the left spine. In a height-balanced subtree every path gives this count. -/
def blackHeight : RBNode → Nat
  | .nil => 0
  | .node .red _ l _ => blackHeight l
  | .node .black _ l _ => blackHeight l + 1

def Balanced : RBNode → Prop
  | .nil => True
  | .node _ _ l r => Balanced l ∧ Balanced r ∧ blackHeight l = blackHeight r

def NoRedRed : RBNode → Prop
  | .nil => True
  | .node color _ l r =>
    NoRedRed l ∧ NoRedRed r ∧ (color = .red → rootColor l = .black ∧ rootColor r = .black)

structure BlackAt (t : RBNode) (h : Nat) : Prop where
  black : rootColor t = .black
  colors : NoRedRed t
  balanced : Balanced t
  height : blackHeight t = h

/-- A black parent adds one black node to every path through either child. -/
theorem BlackAt.join {l r : RBNode} {h : Nat} (hl : BlackAt l h) (hr : BlackAt r h)
    (key : Nat) : BlackAt (node .black key l r) (h + 1) :=
  ⟨rfl, ⟨hl.colors, hr.colors, by simp⟩,
    ⟨hl.balanced, hr.balanced, hl.height.trans hr.height.symm⟩,
    congrArg (· + 1) hl.height⟩

def afterDeletion (x a b c : RBNode) : RBNode :=
  node .black 20 x (node .black 40 (node .red 30 a b) c)

/-- Try the recoloring used when both children of the black sibling are black. -/
def recolorSibling : RBNode → RBNode
  | .node color p x (.node .black s l r) => node color p x (node .red s l r)
  | t => t

/-- Turn the red inner child outward (CLRS deletion case 3). -/
def rotateSibling : RBNode → RBNode
  | .node color p x (.node .black s (.node .red n a b) c) =>
    node color p x (node .black n a (node .red s b c))
  | t => t

/-- Rotate at the parent and blacken both new children (CLRS deletion case 4). -/
def rotateParent : RBNode → RBNode
  | .node color p x (.node .black n a (.node .red s b c)) =>
    node color n (node .black p x a) (node .black s b c)
  | t => t

spytial_ops repairView : RBNode [
  orientation left left below, orientation right right below,
  align ~(left + right).(left + right) - iden horizontal,
  edgeStyle left noLabels, edgeStyle right noLabels,
  attribute key, attribute color, hideAtom univ - RBNode,
  atomStyle RBNode - color.univ (borderStyle "#64748b" 1) (fillStyle "#ffffff"),
  atomStyle {t : RBNode | @:(t.color) = red}
    (borderStyle "#b91c1c" 2) (fillStyle "#fee2e2"),
  atomStyle {t : RBNode | @:(t.color) = black}
    (borderStyle "#1e293b" 2) (fillStyle "#f1f5f9")
]

/-! ## What does recoloring do?

Run the function on four symbolic subtrees. Their common black height is
enough to see the deficit, without choosing any of their keys or children.
-/

example (x a b c : RBNode) (h : Nat)
    (hx : BlackAt x h) (ha : BlackAt a h) (hb : BlackAt b h) (hc : BlackAt c h) : RBNode := by
  have ex := hx.height
  have ea := ha.height
  have eb := hb.height
  have ec := hc.height
  let before := afterDeletion x a b c
  -- What would turning 40 red do to the height gap at 20? Look at 40's left child.
  spytial before observing [blackHeight] with [
    ..repairView, tag univ.(left + right) "bh" blackHeight]
  let trial := recolorSibling before
  spytial trial observing [blackHeight] with [
    ..repairView, tag univ.(left + right) "bh" blackHeight]
  exact trial

/-! ## Why do the two rotations work? -/

/-- Recoloring equalizes the heights but puts two reds together. The two rotations
restore both invariants and leave a black root of height `h + 2`. -/
theorem repair_inner_red (x a b c : RBNode) (h : Nat)
    (hx : BlackAt x h) (ha : BlackAt a h) (hb : BlackAt b h) (hc : BlackAt c h) :
    let t := afterDeletion x a b c
    (Balanced (recolorSibling t) ∧ ¬ NoRedRed (recolorSibling t)) ∧
      ¬ Balanced (rotateSibling t) ∧ BlackAt (rotateParent (rotateSibling t)) (h + 2) := by
  let t := afterDeletion x a b c
  spytial t observing [blackHeight] with [.., attribute blackHeight]
  change (Balanced (recolorSibling t) ∧ ¬ NoRedRed (recolorSibling t)) ∧
    ¬ Balanced (rotateSibling t) ∧ BlackAt (rotateParent (rotateSibling t)) (h + 2)
  -- Unpack the four subtrees' invariants for inspection.
  obtain ⟨cx, nx, bx, ex⟩ := hx
  obtain ⟨ca, na, ba, ea⟩ := ha
  obtain ⟨cb, nb, bb, eb⟩ := hb
  obtain ⟨cc, nc, bc, ec⟩ := hc

  constructor
  · simp [t, afterDeletion, recolorSibling, Balanced, NoRedRed, rootColor,
      blackHeight, bx, ba, bb, bc, ex, ea, eb, ec]

  -- After rotating at 40, which two heights show why we still need to rotate at 20?
  let middle := rotateSibling t
  spytial middle observing [blackHeight] with [
    ..repairView, hideField NoRedRed, hideField Balanced, tag univ.(left + right) "bh" blackHeight]
  constructor
  · intro balanced
    have equalHeights := balanced.2.2
    change blackHeight x = blackHeight a + 1 at equalHeights
    omega
  let repaired := rotateParent middle
  change BlackAt repaired (h + 2)
  -- The new children use (x, a) and (b, c). Each pair has matching black heights.
  have leftOK := BlackAt.join ⟨cx, nx, bx, ex⟩ ⟨ca, na, ba, ea⟩ 20
  have rightOK := BlackAt.join ⟨cb, nb, bb, eb⟩ ⟨cc, nc, bc, ec⟩ 40
  spytial repaired observing [blackHeight] with [
    ..repairView, hideField NoRedRed, hideField Balanced, tag univ.(left + right) "bh" blackHeight]
  exact leftOK.join rightOK 30

end RedBlackDeletion

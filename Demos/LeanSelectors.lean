import SpytialLean

open SpytialLean

/-! # Raw Lean selectors

`lean (…)` takes an ordinary Lean function; its type is its arity: `σ → Bool`
picks out atoms, `σ₁ → σ₂ → Bool` picks out pairs. On a concrete value the
function runs; on a symbolic one the predicate is established from the proof
context instead. -/

inductive Color where
  | red | black
  deriving DecidableEq

inductive RBNode where
  | nil : RBNode
  | node (color : Color) (key : Nat) (left right : RBNode) : RBNode
  -- Selectors compare nodes with `==`, and a `Spytial.Sel`'s results are
  -- located by it, so the type derives `BEq`.
  deriving BEq

def RBNode.height : RBNode → Nat
  | .nil => 0
  | .node _ _ l r => 1 + max l.height r.height

/-- The red-black invariant that a red node has no red child. Two levels of
    pattern matching — the relational language can reach the child's colour, so
    this one has a selector equivalent. -/
def RBNode.redViolation : RBNode → Bool
  | .node .red _ (.node .red ..) _ => true
  | .node .red _ _ (.node .red ..) => true
  | _ => false

/-- Subtree heights differing by more than one. This one has *no* selector
    equivalent: `height` recurses to the leaves, and a relational query cannot
    compute over an unbounded walk. -/
def RBNode.unbalanced : RBNode → Bool
  | .nil => false
  | .node _ _ l r => max l.height r.height - min l.height r.height > 1

/-- The children a node leans away from; the spec below draws an edge to
    each, via the predicate `(p.heavySide).contains c`. -/
def RBNode.heavySide : RBNode → List RBNode
  | .nil => []
  | .node _ _ l r =>
    if l.height > r.height then [l] else if r.height > l.height then [r] else []

/-- `red 5` breaks the colour invariant (its left child is red) *and* leans
    left; the root only leans. -/
def skewed : RBNode :=
  .node .black 10
    (.node .red 5
      (.node .red 3 (.node .black 1 .nil .nil) .nil)
      .nil)
    .nil

spytial_spec RBNode [
  attribute key,
  attribute color,
  orientation left left below,
  orientation right right below,
  hideAtom Color + Nat,
  -- Both of these are Lean, evaluated against whatever value is being drawn.
  atomStyle lean (RBNode.redViolation) (borderStyle "red" 3),
  atomStyle lean (RBNode.unbalanced) (fillStyle "#ffe0e0"),
  -- Lean predicates compose with the relational DSL: this is one selector.
  hideAtom lean (fun n : RBNode => n matches .nil) + Color,
  -- Arity 2. Lowers to `` `a1->`a2 + `a3->`a4 ``.
  inferredEdge heavy lean (fun p c : RBNode => (p.heavySide).contains c) (lineStyle "red" dashed)
]

#spytial skewed

/-! The spec above is stored on the type, with no value in sight. The
predicates run at *use*, once per value — so the same spec highlights different
atoms in a tree that is balanced and legal: -/

def tidy : RBNode :=
  .node .black 10
    (.node .black 5 .nil .nil)
    (.node .black 15 .nil .nil)

#spytial tidy

/-! Inline `with [...]` works the same way, and `#spytial.spec` shows what the
predicate resolved to — the atom ids, which is exactly what spytial-core
evaluates: -/

#spytial.spec skewed with [
  hideAtom lean (fun n : RBNode => n.height > 2),
  inferredEdge heavy lean (fun p c : RBNode => (p.heavySide).contains c)
]

/-! ## The general form

`Spytial.Sel T α` wraps `T → Spytial.Tuples α`. It receives the whole value, so
it can compare nodes against the root, which a per-node predicate never sees.
It needs a fully determined value and executable code. -/

def RBNode.subtrees : RBNode → List RBNode
  | .nil => [.nil]
  | n@(.node _ _ l r) => n :: (l.subtrees ++ r.subtrees)

def deepHalf : Spytial.Sel RBNode RBNode :=
  ⟨fun root => root.subtrees.filter (fun n => 2 * n.height ≤ root.height)⟩

#spytial.spec skewed with [hideAtom lean (deepHalf)]

/-! ## The same predicate during a proof

Before reasoning about a parent, draw what the child-height assumptions say:
the left subtree is height 3, the right is height 1, so the parent is height
4. No key or inner tree needs to be known. The highlight is the same Lean
predicate in the command and in the proof. -/

spytial_ops heightFocus : RBNode [
  attribute key,
  attribute color,
  orientation left left below,
  orientation right right below,
  hideAtom lean (fun n : RBNode => n matches .nil),
  atomStyle lean (fun n : RBNode => n.height = 3) (fillStyle "#dbeafe"),
  flag hideDisconnectedBuiltIns
]

#spytial skewed observing [RBNode.height] with [..heightFocus, attribute height]

example (left right : RBNode) (key : Nat)
    (hLeft : left.height = 3) (hRight : right.height = 1) :
    (RBNode.node .black key left right).height = 4 := by
  let parent := RBNode.node .black key left right
  spytial parent observing [RBNode.height] with [..heightFocus, attribute height]
  simp [RBNode.height, hLeft, hRight]

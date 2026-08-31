import SpytialLean

open SpytialLean

/-! # Raw Lean selectors

`lean (…)` takes an ordinary Lean function; its type is its arity: `σ → Bool`
picks out atoms, `σ₁ → σ₂ → Bool` picks out pairs. -/

inductive Color where
  | red | black
  deriving DecidableEq

inductive RBNode where
  | nil : RBNode
  | node (color : Color) (key : Nat) (left right : RBNode) : RBNode
  -- A `Spytial.Sel`'s results are located by `==`.
  deriving BEq

def RBNode.height : RBNode → Nat
  | .nil => 0
  | .node _ _ l r => 1 + max l.height r.height

def RBNode.redViolation : RBNode → Bool
  | .node .red _ (.node .red ..) _ => true
  | .node .red _ _ (.node .red ..) => true
  | _ => false

/-- No relational equivalent: `height` recurses to the leaves, and a relational
    query cannot compute over an unbounded walk. -/
def RBNode.unbalanced : RBNode → Bool
  | .nil => false
  | .node _ _ l r => max l.height r.height - min l.height r.height > 1

def RBNode.heavySide : RBNode → List RBNode
  | .nil => []
  | .node _ _ l r =>
    if l.height > r.height then [l] else if r.height > l.height then [r] else []

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
  atomStyle lean (RBNode.redViolation) (borderStyle "red" 3),
  atomStyle lean (RBNode.unbalanced) (fillStyle "#ffe0e0"),
  hideAtom lean (fun n : RBNode => n matches .nil) + Color,
  inferredEdge heavy lean (fun p c : RBNode => (p.heavySide).contains c) (lineStyle "red" dashed)
]

#spytial skewed

/-! The spec is stored on the type; the predicates run at use, once per value. -/

def tidy : RBNode :=
  .node .black 10
    (.node .black 5 .nil .nil)
    (.node .black 15 .nil .nil)

#spytial tidy

/-! `#spytial.spec` shows what the predicate resolved to: the atom ids. -/

#spytial.spec skewed with [
  hideAtom lean (fun n : RBNode => n.height > 2),
  inferredEdge heavy lean (fun p c : RBNode => (p.heavySide).contains c)
]

/-! ## The general form

`Spytial.Sel T α` wraps `T → Spytial.Tuples α`. It receives the whole value, so
it can compare nodes against the root, which a per-node predicate never sees. -/

def RBNode.subtrees : RBNode → List RBNode
  | .nil => [.nil]
  | n@(.node _ _ l r) => n :: (l.subtrees ++ r.subtrees)

def deepHalf : Spytial.Sel RBNode RBNode :=
  ⟨fun root => root.subtrees.filter (fun n => 2 * n.height ≤ root.height)⟩

#spytial.spec skewed with [hideAtom lean (deepHalf)]

import SpytialLean

open SpytialLean

/-! # Spytial Demo

Examples of using `#spytial` to visualize Lean data structures.
-/

/-! ## Red-Black Tree

The canonical Spytial example — matches the Rust (caraspace) and Python (spytial-py) demos.
-/

inductive Color where
  | red | black
  deriving Repr

inductive RBNode where
  | nil : RBNode
  | node : Color → Nat → RBNode → RBNode → RBNode
  deriving Repr

spytial_spec RBNode [
  .attribute (field := "node_1"),
  .attribute (field := "node_0"),
  .orientation (selector := "node_2") (directions := [.left, .below]),
  .orientation (selector := "node_3") (directions := [.right, .below]),
  .hideAtom (selector := "Color + Nat"),
  .atomColor (selector := "{x : RBNode | @:(x.node_0) = red}") (value := "red"),
  .atomColor (selector := "{x : RBNode | @:(x.node_0) = black}") (value := "black")
]

def exampleRBTree : RBNode :=
  .node .black 10
    (.node .red 5
      (.node .black 3 .nil .nil)
      (.node .black 7 .nil .nil))
    (.node .red 15
      (.node .black 12 .nil .nil)
      (.node .black 20 .nil .nil))

-- Uses the spec attached to RBNode
#spytial exampleRBTree

/-! ## Binary Tree -/

inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

spytial_spec Tree [
  .orientation (selector := "node_0") (directions := [.left, .below]),
  .orientation (selector := "node_1") (directions := [.right, .below]),
  .hideAtom (selector := "Nat")
]

def myTree : Tree Nat :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3))

#spytial myTree

-- Override with inline spec
#spytial myTree with [
  .orientation (selector := "node_0") (directions := [.above]),
  .orientation (selector := "node_1") (directions := [.above]),
  .atomColor (selector := "leaf") (value := "#0066ff"),
  .hideAtom (selector := "Nat")
]

/-! ## Structures -/

structure Person where
  name : String
  age : Nat

def alice : Person := { name := "Alice", age := 30 }

#spytial alice with [
  .attribute (field := "name"),
  .attribute (field := "age"),
  .atomColor (selector := "Person") (value := "#4CAF50")
]

/-! ## Lists -/

def myList : List Nat := [1, 2, 3, 4]

#spytial myList with [
  .hideAtom (selector := "Nat")
]

/-! ## Free layout (no spec) -/

#spytial myTree

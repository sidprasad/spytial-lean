import SpytialLean

open SpytialLean

/-! # Showcase

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
  | node (color : Color) (key : Nat) (left : RBNode) (right : RBNode) : RBNode
  deriving Repr

spytial_spec RBNode [
  .attribute (field := "key"),
  .attribute (field := "color"),
  .orientation (selector := "left - RBNode->{x : RBNode | @:x = nil }") (directions := [.left, .below]),
  .orientation (selector := "right - RBNode->{x : RBNode | @:x = nil }") (directions := [.right, .below]),
  .hideAtom (selector := "Color + Nat"),
  .hideAtom (selector := "{x : RBNode | @:x = nil }"),
  .atomColor (selector := "{x : RBNode | @:(x.color) = red}") (value := "red"),
  .atomColor (selector := "{x : RBNode | @:(x.color) = black}") (value := "black")
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
  | leaf (value : α) : Tree α
  | node (left : Tree α) (right : Tree α) : Tree α

spytial_spec Tree [
  .orientation (selector := "left") (directions := [.left, .below]),
  .orientation (selector := "right") (directions := [.right, .below]),
  .hideAtom (selector := "Nat")
]

def myTree : Tree Nat :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3))

#spytial myTree

-- Override with inline spec
#spytial myTree with [
  .orientation (selector := "left") (directions := [.above]),
  .orientation (selector := "right") (directions := [.above]),
  .atomColor (selector := "Tree") (value := "#0066ff"),
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

/-! ## Spec Inheritance (Structure extends)

Specs compose across the structure parent chain.
Parent ops come first; child ops extend or override them.
-/

structure Vehicle where
  make : String
  year : Nat

spytial_spec Vehicle [
  .attribute (field := "make"),
  .attribute (field := "year"),
  .atomColor (selector := "Vehicle") (value := "#4CAF50"),
  .hideAtom (selector := "String + Nat")
]

structure Car extends Vehicle where
  doors : Nat

-- Car inherits Vehicle's spec automatically (no spytial_spec needed)
def myCar : Car := { make := "Sedan", year := 2024, doors := 4 }

#spytial myCar

structure ElectricCar extends Car where
  range : Nat

spytial_spec ElectricCar [
  .attribute (field := "range"),
  .attribute (field := "doors"),
  .atomColor (selector := "ElectricCar") (value := "#2196F3")
]

-- ElectricCar's effective spec = Vehicle's ops ++ ElectricCar's ops
def myEV : ElectricCar := { make := "Volt", year := 2025, doors := 4, range := 300 }

#spytial myEV

/-! ## Lists -/

def myList : List Nat := [1, 2, 3, 4]

#spytial myList with [
  .hideAtom (selector := "Nat")
]

/-! ## Debugging -/

-- See the generated YAML spec (hover to inspect in infoview)
#spytial.spec myTree with [
  .orientation (selector := "left") (directions := [.left, .below]),
  .hideAtom (selector := "Nat")
]

-- See the generated JSON data instance (shows relation names)
#spytial.datum myTree

/-! ## Free layout (no spec) -/

#spytial myTree

/-! ## Tactic mode

Use `spytial` as a tactic to visualize data structures mid-proof.
Hypothesis names and local bindings are in scope.
-/

-- Visualize a hypothesis


-- We need to think about what visualizing somethign within a hypothesis
-- even means. Right now, there isn't anything to
-- "visualize"
set_option linter.unusedVariables false in
example (t : RBNode) : True := by
  spytial t
  trivial

-- Inline expression with spec override
example : True := by
  spytial exampleRBTree
  trivial

set_option linter.unusedVariables false in
example (t : Color) : True := by
  spytial t
  trivial

import SpytialLean

open SpytialLean

/-! # Showcase -/

/-! ## Red-Black Tree

Matches the Rust (caraspace) and Python (spytial-py) demos. -/

inductive Color where
  | red | black
  deriving Repr

inductive RBNode where
  | nil : RBNode
  | node (color : Color) (key : Nat) (left : RBNode) (right : RBNode) : RBNode
  deriving Repr

spytial_spec RBNode [
  attribute key,
  attribute color,
  orientation left - RBNode->{x : RBNode | @:x = nil} left below,
  orientation right - RBNode->{x : RBNode | @:x = nil} right below,
  hideAtom Color + Nat,
  hideAtom {x : RBNode | @:x = nil},
  atomStyle {x : RBNode | @:(x.color) = red} (borderStyle "red"),
  atomStyle {x : RBNode | @:(x.color) = black} (borderStyle "black")
]

def exampleRBTree : RBNode :=
  .node .black 10
    (.node .red 5
      (.node .black 3 .nil .nil)
      (.node .black 7 .nil .nil))
    (.node .red 15
      (.node .black 12 .nil .nil)
      (.node .black 20 .nil .nil))

#spytial exampleRBTree

inductive Tree (α : Type) where
  | leaf (value : α) : Tree α
  | node (left : Tree α) (right : Tree α) : Tree α

spytial_spec Tree [
  orientation left left below,
  orientation right right below,
  hideAtom Nat
]

def myTree : Tree Nat :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3))

#spytial myTree

#spytial myTree with [
  orientation left above,
  orientation right above,
  atomStyle Tree (borderStyle "#0066ff"),
  hideAtom Nat
]

structure Person where
  name : String
  age : Nat

def alice : Person := { name := "Alice", age := 30 }

#spytial alice with [
  attribute name,
  attribute age,
  atomStyle Person (borderStyle "#4CAF50")
]

/-! ## Spec Inheritance (Structure extends)

Parent ops come first; child ops extend or override them. -/

structure Vehicle where
  make : String
  year : Nat

spytial_spec Vehicle [
  attribute make,
  attribute year,
  atomStyle Vehicle (borderStyle "#4CAF50"),
  hideAtom String + Nat
]

structure Car extends Vehicle where
  doors : Nat

def myCar : Car := { make := "Sedan", year := 2024, doors := 4 }

#spytial myCar

structure ElectricCar extends Car where
  range : Nat

spytial_spec ElectricCar [
  attribute range,
  attribute doors,
  atomStyle ElectricCar (borderStyle "#2196F3")
]

def myEV : ElectricCar := { make := "Volt", year := 2025, doors := 4, range := 300 }

#spytial myEV

def myList : List Nat := [1, 2, 3, 4]

#spytial myList with [
  hideAtom Nat
]

/-! ## Debugging -/

#spytial.spec myTree with [
  orientation left left below,
  hideAtom Nat
]

#spytial.datum myTree

#spytial myTree

/-! ## Tactic mode -/

-- We need to think about what visualizing somethign within a hypothesis
-- even means. Right now, there isn't anything to
-- "visualize"
set_option linter.unusedVariables false in
example (t : RBNode) : True := by
  spytial t
  trivial

example : True := by
  spytial exampleRBTree
  trivial

set_option linter.unusedVariables false in
example (t : Color) : True := by
  spytial t
  trivial

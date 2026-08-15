import SpytialLean
import Showcase

/-! # Render-test cases

`#spytial_snapshot` (`SpytialLean.Snapshot`) writes `cases/<name>/props.json` for
`render.spec.mjs` to screenshot and diff. The props come from
`spytialPayloadProps`, so a case cannot drift from what the infoview receives.

Run via `just render`. Deliberately a plain (non-`module`) file, like the demos,
so it can use the library's meta surface without module-system ceremony.
-/

open SpytialLean

/-! ## Cases

One per distinct visual feature. Values and specs come from the demos, so these
snapshots track what a user of the demo files actually sees (exception:
`group-align`, below).
-/

-- Red-black tree: nil-hiding, key/color attributes, node coloring by field label.
#spytial_snapshot "rbtree" exampleRBTree

-- Attached polymorphic-type spec (lenient scope).
#spytial_snapshot "tree" myTree

-- Inline `with` override of an attached spec.
#spytial_snapshot "tree-inline" myTree with [
  orientation left above,
  orientation right above,
  atomStyle Tree (borderStyle "#0066ff"),
  hideAtom Nat
]

-- Structure with attribute ops only (no constraints).
#spytial_snapshot "person" alice with [
  attribute name,
  attribute age,
  atomStyle Person (borderStyle "#4CAF50")
]

-- Spec inheritance: Vehicle ops ++ ElectricCar ops.
#spytial_snapshot "ev" myEV

-- Plain list, scalar atoms hidden.
#spytial_snapshot "list" myList with [
  hideAtom Nat
]

-- No spec at all (Person has none attached): the `cndSpec` prop is absent,
-- exercising the widget's free-layout path.
#spytial_snapshot "person-free" alice

-- Purpose-built (not from a demo): group boxes, align, and per-field edge
-- colors — visual features no current demo exercises.
structure TreePair where
  left : Tree Nat
  right : Tree Nat

def duo : TreePair := { left := .node (.leaf 1) (.leaf 2), right := .leaf 3 }

#spytial_snapshot "group-align" duo with [
  group Tree grove,
  align {x, y : Tree | x != y} horizontal,
  edgeStyle left (lineStyle "#e91e63" solid),
  edgeStyle right (lineStyle "#0066ff" solid),
  hideAtom Nat
]

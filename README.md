# spytial-lean

Spytial integration for Lean 4. Visualize Lean data structures as spatial diagrams directly in the VS Code infoview.

## Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.24.0)
- [VS Code](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
- [Node.js](https://nodejs.org/) (for building the widget JS)
- spytial-core built (`cd ../spytial-core && npm run build:browser`)

## Quick start

```sh
# Clone and build
cd spytial-lean
lake update
lake build

# Open in VS Code
code .
```

Open `Demo.lean` and place your cursor on a `#spytial` line. The infoview panel will show the diagram.

## Usage

### Basic visualization

Import `SpytialLean` and use `#spytial` with any term:

```lean
import SpytialLean
open SpytialLean

def myList : List Nat := [1, 2, 3]
#spytial myList
```

The relationalizer walks the expression, turning constructors into nodes and arguments into edges.

### Layout operations

Pass a `with [...]` block to control how the diagram is laid out:

```lean
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def t := Tree.node (.leaf 1) (.node (.leaf 2) (.leaf 3))

#spytial t with [
  .orientation (selector := "node_0") (directions := [.left, .below]),
  .orientation (selector := "node_1") (directions := [.right, .below]),
  .hideAtom (selector := "Nat")
]
```

### Attaching specs to types

Use `spytial_spec` to attach a default layout to a type. Any `#spytial` call on a value of that type will use it automatically:

```lean
spytial_spec Tree [
  .orientation (selector := "node_0") (directions := [.left, .below]),
  .orientation (selector := "node_1") (directions := [.right, .below]),
  .hideAtom (selector := "Nat")
]

-- Uses the attached spec automatically
#spytial t
```

An explicit `with [...]` overrides the attached spec.

### Red-Black Tree example

The canonical Spytial example, matching the Python and Rust versions:

```lean
inductive Color where
  | red | black

inductive RBNode where
  | nil : RBNode
  | node : Color → Nat → RBNode → RBNode → RBNode

spytial_spec RBNode [
  .attribute (field := "node_1"),
  .attribute (field := "node_0"),
  .orientation (selector := "node_2") (directions := [.left, .below]),
  .orientation (selector := "node_3") (directions := [.right, .below]),
  .hideAtom (selector := "Color + Nat"),
  .atomColor (selector := "{x : RBNode | @:(x.node_0) = red}") (value := "red"),
  .atomColor (selector := "{x : RBNode | @:(x.node_0) = black}") (value := "black")
]

def myRBTree : RBNode :=
  .node .black 10
    (.node .red 5
      (.node .black 3 .nil .nil)
      (.node .black 7 .nil .nil))
    (.node .red 15
      (.node .black 12 .nil .nil)
      (.node .black 20 .nil .nil))

#spytial myRBTree
```

## Available operations

Operations are constructors of `SpytialOp`. Pass them as a list to `with [...]` or `spytial_spec`.

### Layout constraints

| Operation | Description |
|-----------|-------------|
| `.orientation (selector) (directions)` | Position source above/below/left/right of target |
| `.align (selector) (direction)` | Align selected elements horizontally or vertically |
| `.cyclic (selector) (direction)` | Arrange elements in a circle (clockwise/counterclockwise) |
| `.group (selector) (name)` | Group selected elements with a bounding box |
| `.hideAtom (selector)` | Hide elements matching the selector |
| `.size (selector) (width) (height)` | Set node dimensions |

### Visual directives

| Operation | Description |
|-----------|-------------|
| `.atomColor (selector) (value)` | Color nodes (any CSS color) |
| `.edgeColor (field) (value)` | Color edges for a relation |
| `.hideField (field)` | Hide all edges for a relation |
| `.attribute (field)` | Display a relation as a node label instead of an edge |
| `.icon (selector) (path)` | Set a custom icon on nodes |
| `.tag (toTag) (name) (value)` | Add computed attributes to nodes |
| `.inferredEdge (name) (selector)` | Add edges that don't exist in the data |
| `.flag (name)` | Set a boolean flag (e.g., `hideDisconnected`) |

### Direction values

`Direction`: `.above`, `.below`, `.left`, `.right`, `.directlyAbove`, `.directlyBelow`, `.directlyLeft`, `.directlyRight`

`AlignDir`: `.horizontal`, `.vertical`

`RotationDir`: `.clockwise`, `.counterclockwise`

`EdgeStyle`: `.solid`, `.dashed`, `.dotted`

## How it works

1. **Relationalizer** (`SpytialLean/Relationalizer.lean`) — Walks the Lean `Expr` tree after WHNF reduction. Constructors become atoms (nodes), data arguments become relations (edges). Type and proof arguments are skipped.

2. **Spec** (`SpytialLean/Spec.lean`) — Typed Lean operations serialize to YAML for spytial-core's layout engine.

3. **Widget** (`widget/src/spytialWidget.tsx`) — A ProofWidgets4 widget module that loads spytial-core, generates a layout from the relational data + spec, and renders via the `webcola-cnd-graph` web component.

### Selector field names

The relationalizer names relations after constructor arguments by index: `node_0`, `node_1`, etc. For example, `RBNode.node : Color → Nat → RBNode → RBNode → RBNode` produces relations `node_0` (Color), `node_1` (Nat), `node_2` (left child), `node_3` (right child). Structure fields use their actual field names.

## Project structure

```
SpytialLean/
  Types.lean          -- JSON-serializable data instance types
  Spec.lean           -- SpytialOp, SpytialSpec, Direction, etc.
  Relationalizer.lean -- Expr walker producing atoms + relations
  Widget.lean         -- ProofWidgets4 widget module registration
  Attr.lean           -- Environment extension for spytial_spec
  Command.lean        -- #spytial command and spytial_spec elaborators
widget/
  src/spytialWidget.tsx  -- React component rendering the diagram
  rollup.config.js       -- Bundles spytial-core into the widget
```

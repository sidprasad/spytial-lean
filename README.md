# spytial-lean

Spytial integration for Lean 4. Visualize Lean data structures as spatial diagrams directly in the VS Code infoview.

## Installation

Add to your `lakefile.lean`:

```lean
require spytialLean from
  git "https://github.com/sidprasad/spytial-lean" @ "v0.1.0"
```

Then run:

```sh
lake update
lake build
```

Pre-built artifacts are downloaded automatically from GitHub Releases. **Node.js is NOT required.**

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.24.0)
- [VS Code](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

### Building from source

If you want to build from source (e.g., for development), you will also need:

- [Node.js](https://nodejs.org/) (for building the widget JS)

```sh
git clone https://github.com/sidprasad/spytial-lean.git
cd spytial-lean
lake update
lake build
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
  | leaf (value : α) : Tree α
  | node (left : Tree α) (right : Tree α) : Tree α

def t := Tree.node (.leaf 1) (.node (.leaf 2) (.leaf 3))

#spytial t with [
  .orientation (selector := "left") (directions := [.left, .below]),
  .orientation (selector := "right") (directions := [.right, .below]),
  .hideAtom (selector := "Nat")
]
```

Selectors use the **constructor parameter names** you define. Named arguments like `(left : Tree α)` produce a relation called `"left"`. Structure fields also use their declared names.

### Attaching specs to types

Use `spytial_spec` to attach a default layout to a type. Any `#spytial` call on a value of that type will use it automatically:

```lean
spytial_spec Tree [
  .orientation (selector := "left") (directions := [.left, .below]),
  .orientation (selector := "right") (directions := [.right, .below]),
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
  | node (color : Color) (key : Nat) (left : RBNode) (right : RBNode) : RBNode

spytial_spec RBNode [
  .attribute (field := "key"),
  .attribute (field := "color"),
  .orientation (selector := "left") (directions := [.left, .below]),
  .orientation (selector := "right") (directions := [.right, .below]),
  .hideAtom (selector := "Color + Nat"),
  .atomColor (selector := "{x : RBNode | @:(x.color) = red}") (value := "red"),
  .atomColor (selector := "{x : RBNode | @:(x.color) = black}") (value := "black")
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

### Debugging

Use `#spytial.datum` and `#spytial.spec` to inspect what the relationalizer and spec serializer produce:

```lean
-- See the JSON data instance (atoms + relations with their names)
#spytial.datum myTree

-- See the generated YAML spec
#spytial.spec myTree with [
  .orientation (selector := "left") (directions := [.left, .below])
]
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

### Relation naming

Relations are named after the constructor parameter names you define:

```lean
inductive Tree (α : Type) where
  | leaf (value : α) : Tree α
  | node (left : Tree α) (right : Tree α) : Tree α
```

This produces relations named `value`, `left`, `right`. Use `#spytial.datum` to see the exact names. Structure fields use their declared field names directly.

If constructor arguments are unnamed (positional style `| node : Tree α → Tree α → Tree α`), the relationalizer falls back to `ctorName_index` (e.g., `node_0`, `node_1`).

### Error handling

When constraints are unsatisfiable, the widget:
- Renders a **counterfactual diagram** using the Maximal Feasible Subset (MFS)
- Shows the **Irreducible Infeasible Subsystem (IIS)** — the minimal set of conflicting constraints
- Highlights related constraints on hover (bidirectional source/diagram cross-highlighting)
- Reports selector evaluation errors separately

This uses spytial-core's `ErrorMessageModal` component directly.

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

See [DEVGUIDE.md](DEVGUIDE.md) for build details and development workflow.

### Spec inheritance

Specs compose across Lean's structure hierarchy. If type `B extends A`, and `A` has a `spytial_spec`, then `B` inherits it automatically. If `B` also has its own `spytial_spec`, the two are composed — parent ops first, child ops appended:

```lean
structure Vehicle where
  make : String
  year : Nat

spytial_spec Vehicle [
  .attribute (field := "make"),
  .attribute (field := "year"),
  .hideAtom (selector := "String + Nat")
]

structure ElectricCar extends Vehicle where
  range : Nat

spytial_spec ElectricCar [
  .attribute (field := "range"),
  .atomColor (selector := "ElectricCar") (value := "#2196F3")
]

-- Effective spec = Vehicle's ops ++ ElectricCar's ops
#spytial myTesla
```

An explicit `with [...]` still fully overrides the inherited spec.

## TODO

- Better integration with Lean's tactic mode (`spytial` tactic, panel widgets)

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

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.32.0)
- [VS Code](https://code.visualstudio.com/) with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

### Building from source

If you want to build from source (e.g., for development), you will also need:

- [Node.js](https://nodejs.org/) with [pnpm](https://pnpm.io/installation) ≥ 9.5 —
  for building the widget JS (`lake build` shells `pnpm install`, and the
  workspace catalog needs 9.5+). The Nix dev shell already provides both.

```sh
git clone https://github.com/sidprasad/spytial-lean.git
cd spytial-lean
lake update
lake build
```

Open a file in `demos/` and place your cursor on a `#spytial` line. The infoview panel will show the diagram.

### Nix dev shell

A [flake](flake.nix) provides a dev shell (elan + Node + pnpm + just) — run `nix develop`. To opt into [direnv](https://direnv.net/): `ln -s nix/envrc .envrc && direnv allow`.

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

Pass a `with [...]` block to control how the diagram is laid out. Ops and
selectors are Lean syntax, not strings:

```lean
inductive Tree (α : Type) where
  | leaf (value : α) : Tree α
  | node (left : Tree α) (right : Tree α) : Tree α

def t := Tree.node (.leaf 1) (.node (.leaf 2) (.leaf 3))

#spytial t with [
  orientation left left below,
  orientation right right below,
  hideAtom Nat
]
```

The elaborator checks each name against the data vocabulary of the type.
`left` and `right` must be relations of `Tree`; relation names come from the
constructor parameter names. `Nat` resolves like a Lean name. A wrong name
causes a compile error with a suggestion: `unknown name 'lft' (did you mean
'left'?)`.

### Attaching specs to types

Use `spytial_spec` to attach a default layout to a type. Any `#spytial` call on a value of that type will use it automatically:

```lean
spytial_spec Tree [
  orientation left left below,
  orientation right right below,
  hideAtom Nat
]

-- Uses the attached spec automatically
#spytial t
```

The target resolves like a Lean name, so `open` works. The spec is stored
structurally in the environment and survives into downstream modules. An
explicit `with [...]` overrides the attached spec.

### Red-Black Tree example

The canonical Spytial example, matching the Python and Rust versions:

```lean
inductive Color where
  | red | black

inductive RBNode where
  | nil : RBNode
  | node (color : Color) (key : Nat) (left : RBNode) (right : RBNode) : RBNode

spytial_spec RBNode [
  attribute key,
  attribute color,
  orientation left left below,
  orientation right right below,
  hideAtom Color + Nat,
  atomStyle {x : RBNode | @:(x.color) = red} (borderStyle "red"),
  atomStyle {x : RBNode | @:(x.color) = black} (borderStyle "black")
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

The `red` and `black` in the label comparisons are the `Color.red` and
`Color.black` constructors, resolved and checked. Renaming a constructor
causes a compile error in the spec.

### Debugging

Use `#spytial.datum` and `#spytial.spec` to inspect what the relationalizer and spec serializer produce:

```lean
-- See the JSON data instance (atoms + relations with their names)
#spytial.datum myTree

-- See the generated spec
#spytial.spec myTree with [
  orientation left left below
]
```

## Coverage checking

`#spytial.coverage` enumerates the data types (`Type`-valued inductives and
structures) under a namespace and warns on any that have no attached
`spytial_spec`, no custom relationalizer, and no explicit waiver:

```lean
spytial_opt_out Tree.Internal "not worth diagramming"

#spytial.coverage Tree
```

`#spytial.coverage!` errors instead of warning — place it in a module that
`lake build` elaborates, and the build fails whenever the library grows a
type nobody has visualized yet.

## The selector language

Selectors replicate Forge's relational expression/formula grammar, embedded
as Lean syntax: `hideAtom {x : RBNode | @:(x.color) = red}` is checked
syntax, not a string. Every name resolves against the target type's data
vocabulary and every operator's arity is checked, so a typo or a renamed
field is a compile error, not an empty selection at render time.

The grammar (EBNF), the integer/value typing rules, and the checking
semantics are in [docs/selectors.md](docs/selectors.md).

## Available operations

Ops go in a bracketed, comma-separated list after `spytial_spec <Type>` or
`#spytial <term> with`.

### Layout constraints

| Operation | Description |
|-----------|-------------|
| `orientation <sel> <dir>+` | Position edge targets relative to sources |
| `align <sel> horizontal\|vertical` | Align selected pairs |
| `cyclic <sel> [clockwise\|counterclockwise]` | Arrange elements in a circle |
| `group <sel> <name> [(addEdge <dir> [(lineStyle …)])]` | Group elements with a bounding box |
| `hideAtom <sel>` | Hide elements matching the selector |
| `size <sel> <width> <height>` | Set node dimensions |

### Visual directives

| Operation | Description |
|-----------|-------------|
| `atomStyle <sel> <block>+ [labels\|noLabels]` | Style nodes |
| `edgeStyle <field> (lineStyle …) [labels\|noLabels]` | Style a relation's edges |
| `hideField <field>` | Hide all edges for a relation |
| `attribute <field>` | Display a relation as a node label instead of an edge |
| `tag <sel> <name> <value>` | Add computed attributes to nodes |
| `inferredEdge <name> <sel> [(lineStyle …)]` | Add edges that don't exist in the data |
| `flag <name>` | Set a boolean flag (e.g., `hideDisconnected`) |

Style ops take parenthesized blocks, matching the rest of the Spytial
ecosystem; block arguments are order-free (a string is the color or path, an
ident the pattern or placement, a numeral the width or weight):

- `(borderStyle <css-color> [<width>])` and `(fillStyle <css-color>)` — node
  border and interior
- `(iconStyle <path> [full\|badge])` — node icon; `full` fills the box,
  `badge` is a corner marker; `labels`/`noLabels` controls the node label
- `(lineStyle <css-color> [solid\|dashed\|dotted] [<weight>])` — edge lines
- `(addEdge togroup\|fromgroup [(lineStyle …)])` — a drawn edge between a
  group and its key

`<field>` positions take a bare relation name, checked against the vocabulary.
Group and inferred-edge names are in scope for later ops in the same spec.

### Enumerated values

Directions: `above`, `below`, `left`, `right`, `directlyAbove`,
`directlyBelow`, `directlyLeft`, `directlyRight` · Alignment: `horizontal`,
`vertical` · Rotation: `clockwise`, `counterclockwise` · Line patterns:
`solid`, `dashed`, `dotted`

## How it works

1. **Relationalizer** (`SpytialLean/Relationalizer.lean`) — Walks the Lean `Expr` tree after WHNF reduction. Constructors become atoms (nodes), data arguments become relations (edges). Type and proof arguments are skipped.

2. **Selector DSL** (`SpytialLean/Selector.lean`, `SelectorElab.lean`) — Selectors elaborate to a reified AST, checked against the vocabulary derived from `TypeShape`. The checker and the relationalizer share the naming logic, so the checker predicts what the walker emits. Specs are stored structurally; the SGQ strings are produced only in the widget payload.

3. **Widget** (`widget/src/spytialWidget.tsx`) — A ProofWidgets4 widget module that loads spytial-core, generates a layout from the relational data + spec, and renders via the `webcola-cnd-graph` web component.

### Relation naming

Relations are named after the constructor parameter names you define:

```lean
inductive Tree (α : Type) where
  | leaf (value : α) : Tree α
  | node (left : Tree α) (right : Tree α) : Tree α
```

This produces relations named `value`, `left`, `right`. Structure fields use their declared field names directly.

If constructor arguments are unnamed (positional style `| node : Tree α → Tree α → Tree α`), the relationalizer falls back to `ctorName_index` (e.g., `node_0`, `node_1`). The spec elaborator knows the real names either way; a wrong one is a compile error that lists the vocabulary.

### Error handling

When constraints are unsatisfiable, the widget:
- Renders a **counterfactual diagram** using the Maximal Feasible Subset (MFS)
- Shows the **Irreducible Infeasible Subsystem (IIS)** — the minimal set of conflicting constraints
- Highlights related constraints on hover (bidirectional source/diagram cross-highlighting)
- Reports selector evaluation errors separately

This uses spytial-core's `ErrorMessageModal` component directly. Static
selector errors (unknown names, arity mismatches) are Lean elaboration errors
and never reach the widget.

## Project structure

```
SpytialLean/
  Types.lean          -- JSON-serializable data instance types
  Selector.lean       -- Reified selector AST + SGQ lowering
  SelectorElab.lean   -- spytial_sel syntax, vocabulary scopes, checking
  Spec.lean           -- SpytialOp, SpytialSpec, JSON serialization
  TypeShape.lean      -- Shared naming logic (walker + checker source of truth)
  Relationalizer.lean -- Expr walker producing atoms + relations
  Widget.lean         -- ProofWidgets4 widget module registration
  Attr.lean           -- Environment extensions (specs, opt-outs)
  Command.lean        -- #spytial, spytial_spec, the op DSL, tactics
  Coverage.lean       -- #spytial.coverage build-time coverage check
tests/
  TypeShapeTest.lean  -- Naming + walker unit tests
  SelectorTest.lean   -- Golden lowering + checker diagnostics tests
  CoverageTest.lean   -- #spytial.coverage diagnostics tests
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
  attribute make,
  attribute year,
  hideAtom String + Nat
]

structure ElectricCar extends Vehicle where
  range : Nat

spytial_spec ElectricCar [
  attribute range,
  atomStyle ElectricCar (borderStyle "#2196F3")
]

-- Effective spec = Vehicle's ops ++ ElectricCar's ops
#spytial myEV
```

An explicit `with [...]` still fully overrides the inherited spec.

## TODO

- Better integration with Lean's tactic mode (`spytial` tactic, panel widgets)

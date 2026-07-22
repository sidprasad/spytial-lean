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

- [Node.js](https://nodejs.org/) (for building the widget JS)

```sh
git clone https://github.com/sidprasad/spytial-lean.git
cd spytial-lean
lake update
lake build
```

Open a file in `demos/` and place your cursor on a `#spytial` line. The infoview panel will show the diagram.

### Nix dev shell

A [flake](flake.nix) provides a dev shell (elan + Node + just) — run `nix develop`. To opt into [direnv](https://direnv.net/): `ln -s nix/envrc .envrc && direnv allow`.

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

Every name is **checked at elaboration time** against the type's data
vocabulary: `left`/`right` must be relations the relationalizer can emit for
`Tree` (they come from your constructor parameter names), and `Nat` resolves
like any Lean name. A typo is a compile error with a suggestion —
`unknown name 'lft' (did you mean 'left'?)` — not a silently empty selection
at render time.

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

The target resolves like any Lean name (`open` works), and the spec is stored
structurally in the environment, so it survives into downstream modules. An
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
  atomColor {x : RBNode | @:(x.color) = red} "red",
  atomColor {x : RBNode | @:(x.color) = black} "black"
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

Note `red` and `black` in the label comparisons: those are the actual
`Color.red`/`Color.black` constructors, resolved and checked — renaming a
constructor breaks the spec loudly at compile time.

### Debugging

Use `#spytial.datum` and `#spytial.spec` to inspect what the relationalizer and spec serializer produce:

```lean
-- See the JSON data instance (atoms + relations with their names)
#spytial.datum myTree

-- See the generated YAML spec
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

Selectors are Forge-style relational expressions over the diagram's atoms and
relations, embedded as Lean syntax (category `spytial_sel`):

| Form | Meaning |
|------|---------|
| `left`, `app_0` | a field relation (arity 2: parent → child) |
| `RBNode`, `String` | a type sig (arity 1: all atoms of that type) |
| `a + b`, `a - b`, `a & b` | union, difference, intersection |
| `a->b` | product |
| `a . b` (or a glued `x.v`) | relational join |
| `^a`, `*a`, `~a` | transitive closure, reflexive-transitive closure, transpose |
| `{x, y : T \| φ}` | set comprehension (arity = number of binders) |
| `@:e = lit` | label comparison (`@str:`/`@bool:`/`@num:` for typed reads) |

Formulas inside comprehensions use Forge's symbolic connective spellings —
`&&`, `||`, `=>`, `!`, plus `in`, `=`, `!=` — and the multiplicity forms
`some`/`no`/`lone`/`one <sel>`. Label comparisons accept nullary constructors
(`@:x = nil`), string/numeric literals, or another projection (`@:vr = @:(y.v)`).

### What gets checked

The elaborator computes the target type's **data vocabulary** — the reachable
closure of type sigs, field-relation names, and nullary-constructor labels
that the relationalizer can emit — and checks every identifier and every
operator's arity against it. Op positions have arity expectations too:
`hideAtom`/`atomColor` select atoms (arity 1), `orientation`/`align` select
pairs, so `hideAtom left` is a compile error rather than a diagram that
silently hides nothing.

Checking is **strict** exactly when the vocabulary is closed (a monomorphic
type built from monomorphic fields). A type parameter, function-typed field,
or custom relationalizer opens the world: unknown names downgrade to warnings
there, and resolved types (like `Nat` in a `Tree α` spec) pass silently.

## Available operations

Ops go in a bracketed, comma-separated list after `spytial_spec <Type>` or
`#spytial <term> with`.

### Layout constraints

| Operation | Description |
|-----------|-------------|
| `orientation <sel> <dir>+` | Position edge targets relative to sources |
| `align <sel> horizontal\|vertical` | Align selected pairs |
| `cyclic <sel> [clockwise\|counterclockwise]` | Arrange elements in a circle |
| `group <sel> <name> [edge]` | Group elements with a bounding box |
| `hideAtom <sel>` | Hide elements matching the selector |
| `size <sel> <width> <height>` | Set node dimensions |

### Visual directives

| Operation | Description |
|-----------|-------------|
| `atomColor <sel> <css-color>` | Color nodes |
| `edgeColor <field> <css-color> [style]` | Color a relation's edges |
| `hideField <field>` | Hide all edges for a relation |
| `attribute <field>` | Display a relation as a node label instead of an edge |
| `icon <sel> <path> [labels]` | Set a custom icon on nodes |
| `tag <sel> <name> <value>` | Add computed attributes to nodes |
| `inferredEdge <name> <sel> [<css-color>] [style]` | Add edges that don't exist in the data |
| `flag <name>` | Set a boolean flag (e.g., `hideDisconnected`) |

`<field>` positions take a bare relation name, checked against the vocabulary.
Group and inferred-edge names are in scope for later ops in the same spec.

### Enumerated values

Directions: `above`, `below`, `left`, `right`, `directlyAbove`,
`directlyBelow`, `directlyLeft`, `directlyRight` · Alignment: `horizontal`,
`vertical` · Rotation: `clockwise`, `counterclockwise` · Edge styles:
`solid`, `dashed`, `dotted`

## How it works

1. **Relationalizer** (`SpytialLean/Relationalizer.lean`) — Walks the Lean `Expr` tree after WHNF reduction. Constructors become atoms (nodes), data arguments become relations (edges). Type and proof arguments are skipped.

2. **Selector DSL** (`SpytialLean/Selector.lean`, `SelectorElab.lean`) — Selectors elaborate to a reified AST, checked against the vocabulary derived from `TypeShape` (the same naming logic the relationalizer uses, so the checker predicts exactly what the walker emits). Specs are stored structurally; the SGQ strings spytial-core evaluates are produced only in the widget payload.

3. **Widget** (`widget/src/spytialWidget.tsx`) — A ProofWidgets4 widget module that loads spytial-core, generates a layout from the relational data + spec, and renders via the `webcola-cnd-graph` web component.

### Relation naming

Relations are named after the constructor parameter names you define:

```lean
inductive Tree (α : Type) where
  | leaf (value : α) : Tree α
  | node (left : Tree α) (right : Tree α) : Tree α
```

This produces relations named `value`, `left`, `right`. Structure fields use their declared field names directly.

If constructor arguments are unnamed (positional style `| node : Tree α → Tree α → Tree α`), the relationalizer falls back to `ctorName_index` (e.g., `node_0`, `node_1`). Either way the spec elaborator knows the real names — a wrong one is a compile error listing the vocabulary.

### Error handling

When constraints are unsatisfiable, the widget:
- Renders a **counterfactual diagram** using the Maximal Feasible Subset (MFS)
- Shows the **Irreducible Infeasible Subsystem (IIS)** — the minimal set of conflicting constraints
- Highlights related constraints on hover (bidirectional source/diagram cross-highlighting)
- Reports selector evaluation errors separately

This uses spytial-core's `ErrorMessageModal` component directly. Static
selector errors (unknown names, arity mismatches) never reach the widget —
they are Lean elaboration errors.

## Project structure

```
SpytialLean/
  Types.lean          -- JSON-serializable data instance types
  Selector.lean       -- Reified selector AST + SGQ lowering
  SelectorElab.lean   -- spytial_sel syntax, vocabulary scopes, checking
  Spec.lean           -- SpytialOp, SpytialSpec, YAML serialization
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
  render/             -- Image-snapshot tests of the widget in headless Chrome
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
  atomColor ElectricCar "#2196F3"
]

-- Effective spec = Vehicle's ops ++ ElectricCar's ops
#spytial myEV
```

An explicit `with [...]` still fully overrides the inherited spec.

## TODO

- Better integration with Lean's tactic mode (`spytial` tactic, panel widgets)

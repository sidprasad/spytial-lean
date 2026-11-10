# Layout specifications

Attach a default layout to a type with `spytial_spec`. Field names in the spec
come from the structure fields or constructor arguments.

```lean
import SpytialLean

inductive Tree where
  | leaf (value : Nat)
  | node (left right : Tree)

spytial_spec Tree [
  orientation left left below,
  orientation right right below,
  attribute value,
  flag hideDisconnectedBuiltIns
]

def tree := Tree.node (.leaf 1) (.leaf 2)
#spytial tree
#spytial tree with [.., atomStyle Tree (borderStyle "blue")]
```

An explicit `with [...]` supplies the layout for one diagram. Include `..` to
splice in the type's default. Structures inherit parent specs before their own
operations. Use `spytial_ops` to name operations for reuse with `..name`.
Selectors can use the [relational language](selectors.md) or [Lean predicates](lean-selectors.md).

## Layout constraints

| Operation | Description |
|-----------|-------------|
| `orientation <sel> <dir>+` | Position edge targets relative to sources |
| `align <sel> horizontal\|vertical` | Align selected pairs |
| `cyclic <sel> [clockwise\|counterclockwise]` | Arrange elements in a circle |
| `group <sel> <name> [(addEdge <dir> [(lineStyle …)])] [(textStyle …)]` | Group elements with a bounding box |
| `hideAtom <sel>` | Hide elements matching the selector |
| `size [<sel>] <width> <height>` | Set node dimensions |

`orientation`, `align`, `cyclic`, and `group` accept `hold: always` or `hold: never`.

## Visual directives

| Operation | Description |
|-----------|-------------|
| `atomStyle [<sel>] <block>* [labels\|noLabels]` | Style nodes |
| `edgeStyle <field> [(lineStyle …)] [(textStyle …)] [labels\|noLabels] [hidden: true]` | Style a relation's edges |
| `hideField <field>` | Hide all edges for a relation |
| `attribute <field>` | Display a relation as a node label instead of an edge |
| `tag <sel> <name> <value>` | Add computed attributes to nodes |
| `inferredEdge <name> <sel> [(lineStyle …)] [(textStyle …)] [draw: "…"]` | Add edges that don't exist in the data |
| `flag hideDisconnected\|hideDisconnectedBuiltIns` | Set a boolean flag |

`edgeStyle`, `attribute` and `hideField` also take `selector: <sel>` and
`filter: <sel>` to scope the relation's edges.

Style blocks accept arguments in any order. Strings specify colors or paths,
names specify patterns or placement, and numbers specify widths or weights.

- `(borderStyle <css-color> [<width>])` and `(fillStyle <css-color>)` — node
  border and interior
- `(iconStyle <path> [full\|badge])` — node icon. `full` fills the box,
  `badge` is a corner marker. `labels`/`noLabels` controls the node label
- `(lineStyle <css-color> [solid\|dashed\|dotted] [<weight>])` — edge lines
- `(textStyle [small\|normal\|large] [<css-color>])` — label text
- `(addEdge togroup\|fromgroup [(lineStyle …)])` — a drawn edge between a
  group and its key

`<field>` positions take a bare relation name, checked against the vocabulary.
Group and inferred-edge names are in scope for later ops in the same spec.

Directions are `above`, `below`, `left`, `right`, `directlyAbove`,
`directlyBelow`, `directlyLeft`, and `directlyRight`.

## Checking a layout

Use `#spytial.spec tree with [..]` to print the effective default layout and
`#spytial.datum tree` to print the atoms and relations it draws.

For a library, `#spytial.coverage MyNamespace` lists data types that have no
attached spec, registered custom relationalizer, or explicit waiver. Use
`#spytial.coverage! MyNamespace` to make missing coverage a build error.

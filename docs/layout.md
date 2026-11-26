# Layout specifications

Attach a default layout to a type with `spytial_spec`. Structure fields and
named constructor arguments are available as relations.

```lean
import SpytialLean

inductive Tree where
  | leaf (value : Nat)
  | node (left right : Tree)

def height : Tree → Nat
  | .leaf _ => 0
  | .node l r => max (height l) (height r) + 1

spytial_spec Tree [
  orientation left left below,
  orientation right right below,
  attribute value,
  attribute height (textStyle large),
  flag hideDisconnectedBuiltIns
]

def tree := Tree.node (.leaf 1) (.leaf 2)
#spytial tree observing [height]
#spytial tree with [.., atomStyle Tree (borderStyle "blue")]
```

`attribute height (textStyle large)` displays available height values in large
type. An attribute can name a unary data function on the tree or one of its
field types. At an inspection, `observing [height]` asks Lean to compute those
values. The same layout also styles height facts supplied by the proof context.

An explicit `with [...]` supplies the layout for one diagram. Include `..` to
splice in the type's default. Structures inherit parent specs before their own
operations. Use `spytial_ops` to name operations for reuse with `..name`.
Selectors can use the [relational language](selectors.md) or [Lean predicates](lean-selectors.md).

## Defaults inside a proof

Inside `by`, `spytial_spec` sets a default for inspections whose subject has that Lean type.
Each type can have its own layout. For example, this proof gives vertices of type `α` a
reachability edge and gives values of type `β` a different size.

```lean
example (α β : Type) (x y : α) (b : β) (R : α → α → Prop) : R x y → True := by
  spytial_spec α [hideAtom univ - α, inferredEdge reaches lean (R)]
  spytial_spec β [size β 72 40]
  intro h
  spytial x
  spytial b
  trivial
```

The declaration captures `R`. Each inspection uses the evidence available at its own line,
so `spytial x` can draw the edge established by `h`. A declaration applies in its goal and
subsequent subgoals while its captured variables are in scope. The latest applicable default
for a type wins. Include `..` in a local declaration to extend the prior default, or in a
call's `with [...]` to extend the active default for that inspection. [Union-find example](../Demos/UnionFind.lean)

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

With `import SpytialLean`, the Lean VS Code extension highlights selector
binders, types, fields, constructor labels, and operators. In a selector such as
`lean (fun n : BDD => n matches .fls) + BDD`, the `lean` introducer and its
two parentheses share the `macro` semantic token. The body uses ordinary Lean
highlighting and the `+` resumes selector highlighting. For a bolder boundary,
add this rule to your VS Code settings.

```json
{
  "editor.semanticTokenColorCustomizations": {
    "rules": { "macro:lean4": { "bold": true } }
  }
}
```

A hex literal in a color field, such as `(fillStyle "#ffe082")`, gets a swatch when VS Code’s
`editor.colorDecorators` setting is enabled. All four CSS hex lengths work,
including alpha. If a freshly opened file has no swatches, an edit after Lean
finishes loading the import refreshes them.

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

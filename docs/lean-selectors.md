# Lean selectors

## What this is

Every layout op needs a **selector**. A selector says which parts of the diagram
the op applies to. For example, `hideAtom` needs to know which nodes to hide.

Spytial has a relational selector language for this. It looks like this:

```lean
hideAtom {x : RBNode | @:(x.color) = red}
```

`lean (...)` is a second way to write a selector. You write a normal Lean
function over your own type. Spytial runs that function on your data and works
out which nodes and edges it picked.

You do not need to know how Spytial turns a Lean value into a graph. You only
write Lean.

## The example used below

```lean
inductive Color where
  | red | black
  deriving DecidableEq, BEq

inductive RBNode where
  | nil : RBNode
  | node (color : Color) (key : Nat) (left right : RBNode) : RBNode
  deriving BEq

def RBNode.isLeaf : RBNode → Bool
  | .nil => true
  | _ => false

def RBNode.key? : RBNode → Nat
  | .node _ k _ _ => k
  | .nil => 0

def RBNode.leftChild : RBNode → RBNode
  | .node _ _ l _ => l
  | .nil => .nil

def RBNode.children : RBNode → Array RBNode
  | .nil => #[]
  | .node _ _ l r => #[l, r]

def myTree : RBNode :=
  .node .black 10 (.node .red 5 .nil .nil) .nil
```

## A first example

To hide every `nil` leaf, write a function that returns `true` for a leaf:

```lean
#spytial myTree with [
  hideAtom lean (fun n : RBNode => n matches .nil)
]
```

That is the whole feature. The function takes an `RBNode` and returns a `Bool`.
Spytial calls it once for every `RBNode` node in the diagram, and hides the ones
that return `true`.

You can use a named `def` instead of a lambda. This is usually easier to read:

```lean
#spytial myTree with [
  hideAtom lean (RBNode.isLeaf)
]
```

## Syntax

The form is always the keyword `lean`, then a Lean term in round brackets:

```
lean (<any Lean term>)
```

The brackets are required. They tell the parser where the Lean term ends.

## Selecting more than single nodes

Some ops need pairs, not single nodes. `orientation` is one: it places the
second node of each pair relative to the first. `inferredEdge` is another: it
draws an edge for each pair.

The **type of your function** decides how many columns the selector has. There
are three shapes. All three are shorthand for one general form, `Spytial.Sel`,
described further down; use a shape when it fits, and the general form when it
does not.

### Shape 1: return `Bool` or `Prop`

Each argument is one column. Spytial tries every combination of nodes.

```lean
-- 1 argument, so 1 column: picks single nodes
#spytial myTree with [
  hideAtom lean (fun n : RBNode => n matches .nil)
]

-- 2 arguments, so 2 columns: picks pairs
#spytial myTree with [
  orientation lean (fun p c : RBNode => p.key? < c.key?) below
]
```

`p.key? < c.key?` returns a `Prop`, not a `Bool`. Both work. Spytial decides a
`Prop` using its `Decidable` instance.

### Shape 2: return a value

The returned value becomes one extra column. So a function with one argument
gives you pairs.

```lean
-- pairs of (node, its left child)
#spytial myTree with [
  orientation lean (RBNode.leftChild) below
]
```

### Shape 3: return a `List`, `Array`, or `Option`

Same as shape 2, but you can return more than one value, or none. Spytial makes
one pair for each element you return.

```lean
#spytial myTree with [
  inferredEdge kids lean (RBNode.children)
]
```

For three columns, use three arguments, or two arguments and a returned value:

```lean
#spytial myTree with [
  inferredEdge tri lean (fun (n : RBNode) (c : Color) (k : Nat) =>
    n matches .node .black _ _ _ && c == .red && k > 7)
]
```

## Which shape should I use?

The three shapes mean the same thing. A selector picks by **value**, and the
same function written in any shape picks the same tuples. The shapes differ
only in cost.

Any shape is fast: Spytial runs your function as compiled code, the same way
`#eval` does, so even a pair test over a large tree finishes at once. The only
limit is the answer — a selector may select at most 4096 tuples, because a
diagram op over more cannot render legibly.

So use the shape that says what you mean. A test to run is shape 1. "This
node's something" is shape 2 or 3.

## A selector picks by value

A Lean value does not know where it came from. A tree with three `nil` leaves
has three nodes in the diagram, but all three hold the same value, `.nil`.

A Lean selector picks by value. When it picks `.nil`, it picks all three
nodes. There is no way for a Lean function to tell them apart, and Spytial
does not guess:

```lean
#spytial.spec myTree with [
  orientation lean (RBNode.leftChild) below
]
```

The root's left child is the key-5 node. Only one node holds that value, so
the root gets one pair. But `atom_3`'s left child is `.nil`, and three nodes
hold `.nil`, so `atom_3` gets three pairs:

```
`atom_0->`atom_3 + `atom_3->`atom_6 + `atom_3->`atom_7 + `atom_3->`atom_8
  + `atom_6->`atom_6 + `atom_6->`atom_7 + `atom_6->`atom_8
  + `atom_7->`atom_6 + `atom_7->`atom_7 + `atom_7->`atom_8
  + `atom_8->`atom_6 + `atom_8->`atom_7 + `atom_8->`atom_8
```

The last nine pairs are there because `RBNode.leftChild` returns `.nil` when
given `.nil`. That is what the function says, so that is what you get.

If you meant "the node in the left *slot*", that is a question about position,
not value. Position is what the relational language is for:

```lean
orientation left below
```

This is the division of work between the two languages. The relational
language sees positions: `left`, `right`, field names. Lean sees values:
anything Lean can compute. Use each for what it sees.

## The general form: `Spytial.Sel`

The full form of a selector is a plain Lean type:

```lean
Spytial.Sel T α   -- the same type as: T → Spytial.Tuples α
```

A `Sel T α` is a function. Spytial calls it on the value being drawn, at the
moment it draws it. The function returns the tuples to select, as a list that
is read as a set: order and duplicates do not matter. `α` is one column
(`Sel RBNode RBNode`) or a product (`Sel RBNode (RBNode × RBNode)` for pairs).

Because the function receives the whole value, it can say things the per-node
shapes cannot — for example, compare every node against the root:

```lean
#spytial.spec myTree with [
  hideAtom lean ((fun t => (Spytial.walked t).filter (fun n => n.key? < t.key?)
    : Spytial.Sel RBNode RBNode))
]
```

`Spytial.walked t` is the list of values Spytial walked, at whatever type you
use it. It has a meaning only during resolution, so a definition that calls it
must be marked `noncomputable` (Lean tells you when you forget), and
`@[expose]`d if another module uses it:

```lean
noncomputable def smallKeys : Spytial.Sel RBNode RBNode :=
  fun t => (Spytial.walked t).filter (fun n => n.key? < t.key?)

#spytial myTree with [hideAtom lean (smallKeys)]
```

The three shapes are ordinary definitions in this vocabulary, and you can read
them in `SpytialLean/Sel.lean`:

```lean
Sel.ofPred p   -- fun t => (walked t).filter p
Sel.ofFn f     -- fun t => (walked t).map (fun x => (x, f x))
Sel.ofMany f   -- fun t => (walked t).flatMap (fun x => (f x).map (x, ·))
```

Selectors compose inside Lean with `∪`:

```lean
#spytial myTree with [
  hideAtom lean ((Spytial.Sel.ofPred RBNode.isLeaf ∪ smallKeys
    : Spytial.Sel RBNode RBNode))
]
```

One care point: a bare lambda needs the ascription `(… : Spytial.Sel T α)`.
Without it, the lambda's type is a plain arrow, and Spytial reads it as one of
the three shapes.

## When you need `BEq`

A selector that **returns** values — shape 2, shape 3, or a `Sel` — makes
Spytial find the node holding each returned value. Spytial finds them with
`==`, so each returned type needs a `BEq` instance:

```lean
inductive RBNode where
  | nil : RBNode
  | node (color : Color) (key : Nat) (left right : RBNode) : RBNode
  deriving BEq
```

With a derived instance, `==` is structural equality, which is what you want.
A plain predicate (shape 1) returns nothing and needs no instance.

## Seeing what your selector picked

Use `#spytial.spec` to print the result:

```lean
#spytial.spec myTree with [
  hideAtom lean (RBNode.isLeaf)
]
```

You will see this:

```json
{"constraints": [{"hideAtom": {"selector": "`atom_6 + `atom_7 + `atom_8"}}]}
```

`atom_6`, `atom_7` and `atom_8` are node ids: the three `nil` leaves. The `+`
means "or". For pairs you will see `` `atom_0->`atom_3 ``, where `->` joins the
two columns of one pair.

If the selector picked nothing, you will see `none`.

Use `#spytial.datum myTree` to see the full list of nodes and their ids. This is
useful when you want to check which node is which.

## Using it in an attached spec

`lean (...)` works in `spytial_spec` too. Spytial stores your function and runs
it again for each value you draw:

```lean
spytial_spec RBNode [
  hideAtom lean (RBNode.isLeaf),
  atomStyle lean (fun n : RBNode => n.key? > 7) (fillStyle "#ffe0e0")
]

#spytial myTree      -- runs the functions on myTree
#spytial otherTree   -- runs them again on otherTree
```

## Mixing with the relational language

A `lean (...)` selector becomes an ordinary selector once Spytial has run it.
You can combine it with the relational language in the same expression:

```lean
#spytial myTree with [
  hideAtom lean (RBNode.isLeaf) + Color
]
```

This hides every leaf **and** every `Color` node.

## What does not work

These are the current limits. Some are permanent, some are just not built yet.

**You cannot select things that are not values.**
`lean (...)` runs on your Lean data. Some parts of a diagram do not come from
your data:

- group names and inferred edge names that an earlier op created
- relations that the walker invents, such as `scrutinee` for a stuck `match`
- nodes made by a custom relationalizer

Use the relational selector language for those. The two mix freely.

**Open terms are skipped.**
When you draw a proof, or a term with holes, some nodes stand for an unknown.
Your function cannot run on an unknown, so those nodes are never selected. They
are skipped silently.

**A `Prop` runs through `decide`.**
A proposition with a `Decidable` instance works exactly like a `Bool`. One
without is an error at the selector — never a silent empty selection.

**A function from another module must be `meta import`ed.**
A selector runs while Lean elaborates the command, and the module system
requires `meta import` for code that runs at that time. Lean's error message
names the exact import to add. Definitions in the same file need nothing.

**Dependent function types are rejected.**
A function like `(n : Nat) → Fin n → Bool` will not work as a selector.

**A selector selects at most 4-tuples.**
Wider relations are rejected at the selector.

**Two nodes holding the same value cannot be told apart.**
A selector picks by value, and picks every node holding that value. When
position matters, use the relational language. See "A selector picks by
value" above.

**Diagram error messages show node ids, not your Lean code.**
When constraints conflict, the Spytial error panel shows the failing selector.
For a `lean (...)` selector it shows `` `atom_3 + `atom_7 ``, not the function
you wrote. This is a known gap and is planned as a follow-up.

## Errors you may see

| Message | Meaning |
|---------|---------|
| `must be a function over the walked types` | You passed a value, not a function. A selector needs at least one argument. |
| `cannot have a dependent argument type` | See "Dependent function types" above. |
| `must be a closed term` | The term used a local variable from outside the selector. |
| `is not among the types reachable from 'T'` | Your function's argument type never appears in the value being drawn, so it can never match. This is a warning, not an error. |
| `this position selects atoms (arity 1), but the selector has arity 2` | The op wanted single nodes, and your function gives pairs. Drop an argument, or return `Bool` instead of a value. |
| `selects N tuples, over the limit of 4096` | The selector picked more tuples than one diagram op can render. Select less. |
| `needs a Decidable instance to run as a selector` | See "A `Prop` runs through `decide`" above. |
| `add deriving BEq to the returned type` | See "When you need `BEq`" above. |
| `consider adding public meta import ...` | See "A function from another module" above. Lean names the import to add. |
| `calls Spytial.walked inside ...` | `walked` sits in a definition Spytial cannot read into. Call it in the selector term, or `@[expose]` the definition. |
| `can select at most 4-tuples` | The selector is wider than any diagram op. |

## How it works, briefly

You do not need this to use the feature, but it helps when debugging.

1. Spytial walks your value and makes a node for each part it finds. It records
   which part of the value each node came from.
2. It builds one Lean term: your function, plus the recorded values quoted in
   as lists.
3. It runs that term with Lean's compiled evaluator — the same machinery as
   `#eval`. The result is the selected tuples, as positions in the recorded
   lists, and a position is a node.
4. The tuples are written back into the spec as a plain list of ids, for
   example `` `atom_3 + `atom_4 ``. That list is what the rendering engine
   receives; the engine never sees your Lean function.

Step 3 happens when you draw a value, not when you write the spec. That is why
an attached `spytial_spec` gives different ids for different trees.

See [demos/LeanSelectors.lean](../demos/LeanSelectors.lean) for a full working
example, and [selectors.md](selectors.md) for the relational selector language.

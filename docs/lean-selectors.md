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
are three shapes.

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

**Use shape 2 or 3 when you mean "this node's something".** They are faster, and
they give the right answer more often. See the next section for why.

Use shape 1 when there is no value to return, only a test to run.

The cost matters. Shape 1 with two arguments tries every pair. On a tree with
300 nodes that is 90,000 calls. Shape 2 with one argument makes 300 calls.
Spytial stops with an error above 4096 combinations.

## Why shape 2 is usually more correct

A Lean value does not know where it came from. A tree with three `nil` leaves
has three nodes in the diagram, but all three hold the same value, `.nil`.

So this shape 1 selector relates every leaf to every other leaf:

```lean
#spytial.spec myTree with [
  orientation lean (fun p c : RBNode => p.leftChild == c) below
]
```

It picks 13 pairs. `atom_6`, `atom_7` and `atom_8` are the three leaves, and
every combination of them is in the result:

```
`atom_0->`atom_3 + `atom_3->`atom_6 + `atom_3->`atom_7 + `atom_3->`atom_8
  + `atom_6->`atom_6 + `atom_6->`atom_7 + `atom_6->`atom_8
  + `atom_7->`atom_6 + `atom_7->`atom_7 + `atom_7->`atom_8
  + `atom_8->`atom_6 + `atom_8->`atom_7 + `atom_8->`atom_8
```

The shape 2 version does not have this problem. Spytial knows which node it
called the function on, so it picks the child of *that* node:

```lean
#spytial.spec myTree with [
  orientation lean (RBNode.leftChild) below
]
```

It picks 5 pairs, and `atom_3` now has exactly one left child:

```
`atom_0->`atom_3 + `atom_3->`atom_6
  + `atom_6->`atom_6 + `atom_7->`atom_6 + `atom_8->`atom_6
```

The last three pairs are there because `RBNode.leftChild` returns `.nil` when
given `.nil`. That is what the function says, so that is what you get.

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

**A `Prop` needs a `Decidable` instance.**
If Spytial cannot decide your proposition, the node is skipped. Spytial never
guesses. If your selector picks nothing and you expected a match, check this
first.

**Dependent function types are rejected.**
A function like `(n : Nat) → Fin n → Bool` will not work as a selector.

**Two nodes holding the same value cannot be told apart by shape 1.**
See "Why shape 2 is usually more correct" above.

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
| `ranges over N points ... over the limit of 4096` | A shape 1 selector with too many combinations. Rewrite it as shape 2 or 3. |

## How it works, briefly

You do not need this to use the feature, but it helps when debugging.

1. Spytial walks your value and makes a node for each part it finds. It records
   which part of the value each node came from.
2. Your function runs on those recorded parts.
3. What it picked is written back into the spec as a plain list of ids, for
   example `` `atom_3 + `atom_4 ``.
4. That list is what the rendering engine receives. The engine never sees your
   Lean function.

Step 3 happens when you draw a value, not when you write the spec. That is why
an attached `spytial_spec` gives different ids for different trees.

See [demos/LeanSelectors.lean](../demos/LeanSelectors.lean) for a full working
example, and [selectors.md](selectors.md) for the relational selector language.

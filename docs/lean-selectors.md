# Lean selectors

A layout op needs a selector: the set of nodes or tuples it applies to. The
relational language queries the diagram; `lean (…)` runs an ordinary Lean
function over your data instead. Anything Lean can compute is available,
including recursion over your own functions. The form is the keyword `lean`,
then a term in round brackets — the brackets tell the parser where the term
ends.

The example used below:

```lean
inductive Color where
  | red | black
  deriving DecidableEq, BEq

inductive RBNode where
  | nil : RBNode
  | node (color : Color) (key : Nat) (left : RBNode) (right : RBNode)
  deriving BEq

def RBNode.isLeaf : RBNode → Bool
  | .nil => true
  | _ => false

def RBNode.leftChild? : RBNode → Option RBNode
  | .node _ _ l _ => some l
  | .nil => none

def myTree : RBNode :=
  .node .black 10 (.node .red 5 .nil .nil) .nil
```

## Form 1: a predicate

A function returning `Bool` or `Prop` keeps the walked tuples it accepts. Each
argument is one column, up to four; Spytial tries every combination of nodes.
A `Prop` is decided through its `Decidable` instance, so `=` and `<` work.

```lean
-- 1 argument: picks single nodes
#spytial myTree with [hideAtom lean (RBNode.isLeaf)]

-- 2 arguments: picks pairs
#spytial myTree with [
  orientation lean (fun p c : RBNode => p.leftChild? == some c) below
]
```

An accessor spelled as a predicate is the accessor's relation: `p.leftChild?
== some c` selects each node paired with its left child, and a container
accessor is a membership test, `(p.children).contains c`.

## Form 2: `Spytial.Sel`

The general form is a function of the whole value being drawn. `Sel T α` wraps
`select : T → Tuples α`: Spytial calls it on the datum, and the returned
tuples are selected. `α` is one column (`Sel RBNode RBNode`) or a product
(`Sel RBNode (RBNode × RBNode)`); the returned list is read as a set. Build
one with the anonymous constructor, walk your own type inside it — that is
ordinary code:

```lean
def RBNode.subtrees : RBNode → List RBNode
  | .nil => [.nil]
  | n@(.node _ _ l r) => n :: (l.subtrees ++ r.subtrees)

def smallKeys : Spytial.Sel RBNode RBNode :=
  ⟨fun t => t.subtrees.filter (fun n => n.key? < t.key?)⟩

#spytial myTree with [hideAtom lean (smallKeys)]
```

Because it receives the whole value, a `Sel` can say things a predicate
cannot — compare every node against the root, for example. A `Sel` is plain
computable code: run it with `#eval`, test it with `#guard`, compose it with
`∪`.

Spytial locates each returned value by `==`, so every column type needs
`BEq` — `deriving BEq` on your type. A predicate returns nothing and needs no
instance.

## Values are atoms

By default the diagram keys nodes by value — structural identity, derived on
demand — and derived `BEq` computes the same equality, so a value names
exactly one node. `myTree` is written with three `nil` leaves; the diagram has
one `nil` node, and a selector that picks `.nil` picks exactly it.

A type can decline with `instance : SpytialIdentity RBNode := .asWritten`:
then equal values keep one node per occurrence, and no Lean function can tell
them apart. If you mean "the node in the left *slot*", that is position, not
value — the relational language's job (`orientation left below`). The two mix
freely in one expression: `hideAtom lean (RBNode.isLeaf) + Color`.

Use `#spytial.spec` to print what a selector resolved to (node ids like
`` `atom_3 ``, `+` for union, `->` joining tuple columns), and
`#spytial.datum` to see which node is which.

## The rules that bite

- **Closed, non-dependent terms only.** A selector cannot capture local
  variables, and dependent argument types are rejected.
- **`meta import` for other modules.** A selector runs at elaboration time;
  Lean's error names the exact import to add. Same-file definitions need
  nothing.
- **Only values are selectable.** Group names, invented relations
  (`scrutinee`), custom-relationalizer nodes, and open terms (holes,
  hypotheses) never match; use the relational language for those.
- **At most 4 columns, at most 4096 selected tuples.** Wider or bigger cannot
  render legibly.
- **Diagram errors show node ids, not your code.** A conflicting `lean (…)`
  selector reports as `` `atom_3 + `atom_7 `` in the error panel — a known
  gap.

`spytial_spec` stores the function and re-runs it for each value drawn, as
compiled code. [demos/LeanSelectors.lean](../demos/LeanSelectors.lean) is a
worked example; [selectors.md](selectors.md) has the grammar and checking
rules.

# Lean selectors

A layout op needs a selector: the set of nodes or tuples it applies to. The
relational language queries the diagram; `lean (…)` describes a selection
using Lean functions and predicates. Both range over the same relationalized
datum, with Lean terms and evidence retained for its atoms. The form is the keyword `lean`,
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
Closed predicates on closed values run through Lean's compiled evaluator;
`Prop` predicates use `Decidable` when available, so `=` and `<` work.
For symbolic values, direct evidence and bounded simplification can establish
the predicate without determining the entire value. This path needs no
`Decidable` instance. A Boolean predicate matches when it is established to be `true`.

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

Because it receives the whole value, a `Sel` can perform a traversal itself
instead of enumerating represented candidates. A `Sel` is plain
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

## The same selector across contexts

For a tree type with a `height` function, one attached specification can be
used for computed values and for inspection inside a definition or proof:

```lean
spytial_spec Tree [
  atomStyle lean (fun n : Tree => height n = 3) (fillStyle "#dbeafe")
]

#spytial concreteTree

example (t : Tree) (h : height t = 3) : True := by
  spytial t
  trivial
```

In the proof, `t` is selected without knowing its children. In the command,
the same property can be computed. `observing [height]` is not required to
use this predicate: observation adds heights to the datum for display; the
selector only selects among atoms already present. When observations are
requested, their checked equalities are also available to selector resolution.

The domain is the refined, relationalized datum, not every variable in the
surrounding proof. Each candidate has a represented Lean term of the actual
argument type, checked independently of short names and labels. Binary and
wider predicates select tuples of these atoms. Resolution adds no data atoms
or relations; an `inferredEdge` can then display its selected tuples.

Inline predicates may capture parameters in scope:

```lean
spytial t with [
  atomStyle lean (fun n : Tree => height n = threshold) (fillStyle "#dbeafe")
]
```

Symbolic matching first checks retained proofs by definitional equality, then
uses bounded `simp` with ordinary simp rules, computation through available
definitions, the retained context proofs, and observation equations. For
example, child heights `2` and `1` can establish parent height `3`; separate
proofs of `P x` and `Q x` can establish `P x ∧ Q x`. New proofs are kernel-checked.
This is not unrestricted theorem search: no `aesop`, `omega`, or invented
assumptions. Use proved hypotheses or `fyi` when further reasoning is needed.

Missing evidence means no established match, not an established negation.
`lean (fun x => ¬ P x)` needs support for the negation. The same applies to
Boolean `!`. Relational difference, `Tree - lean (P)`, instead means all tree
atoms not selected by `P`, including those whose status is undetermined.

## The rules that bite

- **Non-dependent arguments, no unresolved holes.** Predicates may capture
  local variables, but dependent argument types are rejected. Metavariable
  holes are neither selected nor assigned by resolution.
- **`meta import` for other modules.** A selector runs at elaboration time;
  compiled code from another module must be available via `meta import`.
  Symbolic reduction also needs accessible bodies or suitable lemmas: use
  `@[expose]` for definitions intended to unfold across module boundaries.
  An unavailable body cannot be guessed from a displayed value.
- **A Lean interpretation is required.** Symbolic variables and shared
  existential witnesses can match. Synthetic custom-relationalizer nodes
  without a corresponding term, group names, and invented relation names
  cannot; use the relational language for those.
- **Identity remains the relationalizer's policy.** A coarser classifier can
  merge unequal values. Predicates inspect the drawn representative, not any
  arbitrary member of that class. Refinement aliases are accepted when they
  are established equal to the representative; `.asWritten` occurrences stay distinct.
- **Whole-value programs still need a whole value.** `Spytial.Sel` remains
  executable, closed code. An incomplete root is an explicit error, including
  for an attached spec; the selector is never silently discarded.
- **At most 4 columns, at most 4096 selected tuples.** Wider or bigger cannot
  render legibly. Compiled enumeration is capped at one million points;
  symbolic enumeration includes candidate/evidence comparisons in that bound.
  Simplification is capped at 1,000 steps per check. Limit failures are errors,
  not silently truncated selections.

## What a conflict report shows

A `lean (…)` selector resolves to node ids, so on its own an error panel would
cite `` `atom_3 + `atom_7 `` — true, but unreadable. The emitted spec therefore
carries the Lean you wrote, and spytial-core cites that instead:

```
hideAtom lean (fun n : RBNode => n matches .nil)   (MyTree.lean:12)
```

This applies to the ops that appear in conflict reports — `orientation`,
`align`, `cyclic`, `group` and `hideAtom`, which is the manifest's own
`source.displayedBy`. Everywhere else core parses the stamp and ignores it, so
the spec leaves it off. An attached `spytial_spec` keeps the line it was
declared on, so a spec re-run against another value still points at where it
was written. Turn it off with `set_option spytial.source false` to keep the
emitted spec free of source text.

`spytial_spec` stores the selector and resolves it against each inspection's
datum and evidence. [Demos/LeanSelectors.lean](../Demos/LeanSelectors.lean) is a
worked example; [selectors.md](selectors.md) has the grammar and checking
rules.

# Facts belong to the values being inspected

Tactic-mode `spytial` shows the inspected expression together with relevant,
proof-backed context. A local name should not change which facts are relevant,
and a fact referring to an already represented symbolic subtree should refer
to that same subtree atom.

## Relevant context

IYKYK extracts and checks the facts before Spytial selects the relevant subset.
Spytial starts from the selected root and the symbolic values represented by
its expression walk, including children exposed by known equalities. Local
`let` names are expanded for matching; global observers such as `height` stay
folded.

A fact is retained when a data occurrence in it matches one of these anchors.
Its symbolic data occurrences then become anchors for further facts. This
repeats to a fixed point over the finite set of extracted facts. Selection
preserves the original certified propositions and proofs; it does not perform
additional proof search.

Types, proof terms, typeclass instances, and shared function heads are not
connections between facts. Nor are incidental closed scalars: mentioning `1`
in a height comparison must not pull in every other fact about `1`. A closed
value explicitly selected as the root is still an anchor.

This makes both spellings of an inspection retain the same context:

```lean
let left := Tree.node ll lx lr
let before := Tree.node left x r
spytial before observing [height]
spytial (Tree.node (.node ll lx lr) x r) observing [height]
```

After a rotation, facts about unchanged subtrees remain relevant even if no
hypothesis mentions the new whole tree. A fact about an old parent still refers
to that old parent, not to the new root. The resulting datum can therefore
include old structure needed to express the retained facts.

The widget shows one relational datum: the selected expression together with all
relevant structures and relationships needed by its retained facts. For example,
an after-rotation inspection can include an old parent mentioned by a branch
inequality. This is program knowledge, not a second display mode. Use layout
operations such as `hideAtom`, `hideField`, and selectors to control what the
diagram presents. The context facts are listed below the diagram.

`spytial.datum` prints the same datum. The widget payload additionally records the
selected root and its source term so the infoview can identify what was inspected.

The AVL layout renders `height` and `key` as attributes. It also enables core's
`hideDisconnectedBuiltIns` flag: scalar nodes left unconnected after attribute
folding are hidden, but scalar values participating in context comparisons remain
visible. This is a presentation policy; the datum keeps the scalar values.

Contradiction checks still happen before projection. Inconsistency and
extraction truncation keep their existing behavior. Programmatic callers that
request `rootOnly := false` continue to receive unfiltered extracted knowledge.

## Sharing symbolic subtrees

For classifier-based identity in context mode, repeated occurrences of
the same open constructor term reuse an atom. Local let aliases are normalized
for this comparison, as are Lean's natural-literal encodings. This includes the
default derived structural identity: identical terms necessarily have identical
keys, even when those keys cannot yet be evaluated. Different variables remain
different: `node a k r` is not merged with `node b k r` merely because both have
the same constructor and key. Unknown type parameters are not solved to find an
identity instance.

This also applies when an occurrence is nested inside an observation, such as
`height (node a k r)`. The height relation attaches to the subtree already
reached through the parent's field, rather than to a second copy.

Ordinary command-mode walks, closed-value identity, and custom relationalizers
are unchanged. The shortcut respects the existing type-level identity policy;
it does not apply to `asWritten`, `Raw`, or decider-based identities, which can
deliberately distinguish occurrences. There is no new observation option.

## Observations and relationships

For a known node with unknown children, `observing [height]` records:

```text
height(parent, H)
height(left, HL)
height(right, HR)
```

The observer is evaluated before its result is added. Known child heights can
therefore compute the parent's height. With
`observing [height] dependencies`, named operations in a symbolic simplified
result connect the recursive observations:

```text
max(HL, HR, M)
add(1, M, H)
```

These `max` and `add` tuples relate the symbolic parent and child heights. They
are the residual dependency graph, not a trace of every reduction. An
independently retained fact such as `height r + 1 < height l` can introduce
additional `add` and comparison relationships. See
[Observations](observations.md) for the evaluation and result-representation
contract.

In particular, neither retaining branch inequalities nor observing heights
proves that an arbitrary result is balanced. That requires appropriate
preconditions and a proof.

The datum-level regression tests are in `tests/ContextInspectionTest.lean`.

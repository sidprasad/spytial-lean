# Inspecting a proof

Place the cursor on a theorem's name to see a collapsed **Spytial inspections (n)**
summary in the infoview. Expand it to explore the `spytial` inspections in
its proof. Diagrams and comparison controls are loaded only after expansion.
The points appear in source order. With two or more points, the explorer
initially compares the first and last. Choose any two points with the selectors,
use **Step through** to inspect one point at a time, or choose **All points**.
A theorem with one inspection shows that view after expansion.
Collapsing and reopening the explorer preserves the selected view and points.

Each `spytial` line still has its ordinary infoview widget. The explorer retains
the same payload: inspected term, relational data, resolved layout specification,
observations, extracted proof facts, and the local context at that line.

Titles default to the inspected binder name or the displayed Lean expression.
Add an optional `titled` clause at the end of a tactic for an authored caption:

```lean
theorem exampleInspection (xs : List Nat) : True := by
  let input := xs
  let repaired := 0 :: input
  spytial input observing [List.length]
  spytial repaired observing [List.length] with [attribute length]
    titled "After prepending zero"
  trivial
```

The clause order is `spytial term`, `observing [...]`, `fyi [...]`, `with [...]`,
then `titled "..."`; every clause after the term is optional. Captions do not
change the term or infer anything about the proof.

## Correspondence and layout

These are inspections of a proof, not frames from an execution trace. Source
order alone does not establish that two values are successive states of one
running data structure. Different goals and case branches use independent
layouts, even when their displayed names or traversal IDs coincide.

Within the **same Lean goal**, an exact shared free-variable identity can
establish a correspondence. The adapter retains each atom's Lean local-variable
evidence. It accepts only a one-to-one match of compatible atoms; ambiguous
aliases are ignored. Labels, traversal-local atom IDs, and structural similarity
are not evidence. Rebuilt constructor nodes are not matched by their key fields.
The current implementation is deliberately conservative about correspondence
across tactics that create a new goal, and about terms without local-variable
evidence.

For example, in CLRS-Lean's `redBlackShape_repaint_rotateLeft_red_red`:

```lean
let input := node .red a x (node .red b y c)
let rotated := rotateLeft input
let repaired := repaintRoot .black rotated
spytial input observing [blackHeight]
spytial rotated observing [blackHeight] titled "After rotation"
spytial repaired observing [blackHeight] titled "After repaint"
```

`b` is the same Lean local in all three views, although its traversal-local atom
ID changes from `atom_5` in input and rotated to `atom_6` in repaired. Its parent
moves from the node with key `y` to the
node with key `x`. The adapter remaps `b`'s previous coordinates to its current
atom ID and passes them through core's **stability** sequence policy. It does not
identify the rebuilt `x` and `y` tree nodes with the scalar key variables.

This uses the same `renderLayout(layout, {policy, prevInstance, currInstance,
priorPositions})` gateway used by Cope and Drag. Comparison and all-point panes
wait for the first pane's `layout-complete` event, then use its settled positions
as hints for each other pane. Stepping uses the last settled point. The adapter
masks core's short-lived ID memory to prevent traversal IDs from reviving an
unrelated node. Each pane keeps its actual payload and layout specification.
Core's solver still enforces root/child, left/right, alignment, and other layout
constraints; these coordinates are hints, not new positional constraints.

Stability suits this rotation's pointer rewiring. Change emphasis is useful in
the array-indexed algorithm examples where swaps force visible values to move;
it is not needed to establish Lean identity here. There is no forced alignment
when identity evidence, settled positions, or core's stability API is unavailable:
the views render independently. A status below comparisons explains this fallback.

References inspected for this integration:

- `copeanddrag/packages/sterling/src/components/GraphView/SpyTialGraph.tsx`
- `copeanddrag/packages/sterling/src/components/GraphView/MultiTemporalGraph.tsx`
- `spytial-core/docs/SEQUENCE_LAYOUT_API.md`
- `spytial-clrs/src/algviz/README.md`

## Collection and verification

Named theorems and definitions containing literal `spytial` tactics use a small
declaration elaborator that finishes the proof before attaching the explorer to
the declaration name. Those declarations currently elaborate synchronously and
do not reuse intermediate tactic snapshots. Declarations without inspections use
Lean's ordinary elaborator. Tactics generated entirely by another macro and
anonymous `example` declarations retain their line widgets but do not currently
get a declaration-name explorer.

An environment-owned, nonpersistent journal records the actual tactic payloads.
Lean's tactic backtracking restores this journal, so failed alternatives are
excluded even though Lean retains their diagnostic info trees. The journal is
enabled only during collection and restored in `finally`; it cannot accumulate
points across declarations, edits, imports, or asynchronous proof tasks.

Run:

```sh
pnpm -C widget test
lake build SpytialTests Demos renderHarnessJs
pnpm -C render exec playwright install chromium
node render/infoview-test.mjs
node render/clrs-explorer-test.mjs /absolute/path/to/CLRS-Lean
```

The infoview test starts a real Lean language server, calls
`Lean.Widget.getWidgets` at theorem names and each inspection line, and checks
that `getWidgetSource` serves the current production bundle. Chromium renders
those exact props and exercises pair selection, stepping, all points, and the
single-point view. It also checks sibling-goal isolation, failed alternatives,
and a document edit without stale points.

The optional CLRS test reads the downstream source and generates an excerpt
under `.lake`, retaining the actual theorem statement, proof, definitions, and
layout. It replaces the two inspection bindings with the three bindings above.
It narrows the chapter's `Mathlib` import to the tactic-linter module this
excerpt needs; the mathematical proof is unchanged.
The downstream checkout is unchanged. The test checks `b`'s changed atom IDs and
shared identity, actual stability seeds, and the rendered left/right/below
constraints. Screenshots and props are saved under `.lake` for local review.

import SpytialLean

open SpytialLean

/-! # Notation-aware atom labels (`.notationLabel`)

Lean elaborates notation away before the relationalizer runs, so `[1, 2, 3]`
arrives as a `List.cons 1 (List.cons 2 (List.cons 3 List.nil))` term and renders
as a four-atom cons chain (three `cons` nodes plus the `nil` terminator, with
`head`/`tail` edges). That faithful structural view is often exactly what you
want — but sometimes you would rather see the *surface syntax*.

The `.notationLabel` spec op is an opt-in that collapses every value of a chosen
type to a **single** atom labeled with the pretty-printed (delaborator-resugared)
expression — `[1, 2, 3]`, `(1, 2)`, etc. It is a *relationalizer-side* op: it
configures how terms are walked, not how the diagram is laid out, so it never
appears in the YAML sent to spytial-core (per the project's partitioning rule).

Selectors here use the **type-HEAD short name**, not the full applied type:
write `.notationLabel (selector := "List")`, not `"List Nat"`. The head name is
the same string that fills an atom's `type` field (`List`, `Prod`, …).

Limitation: `.notationLabel` works in `with [...]` blocks only. Type-attached
specs (`spytial_spec`) are stored as YAML and cannot carry it yet; writing one
there is a clear error rather than a silent drop.
-/

/-! ## A list: cons chain vs. one collapsed atom

Plain `#spytial` shows the structural cons chain: atoms `cons`, `cons`, `cons`,
`nil` (all typed `List`) with `head` edges to the `Nat` leaves `1`, `2`, `3` and
`tail` edges chaining them together — four `List` atoms in total.
-/

#spytial ([1, 2, 3] : List Nat)

/-! With `.notationLabel (selector := "List")` the same value becomes ONE atom,
    typed `List`, labeled `[1, 2, 3]`, with no relations. -/

#spytial ([1, 2, 3] : List Nat) with [.notationLabel (selector := "List")]

-- Expected collapsed data instance (one atom, no edges):
--   atoms:     [{ id: atom_0, type: "List", label: "[1, 2, 3]" }]
--   relations: []
-- (The datum debug commands take no `with` block, so the collapsed JSON is noted
--  here rather than printed; `#spytial.datum` below shows the un-collapsed chain.)
#spytial.datum ([1, 2, 3] : List Nat)

/-! ## Nested: the field collapses, the parent decomposes

In `("xs", [1, 2]) : String × List Nat` the `Prod` is NOT in the collapse set, so
it decomposes as usual into `mk` with `fst` / `snd` edges. The `snd` field is a
`List`, which IS collapsed: it becomes a single `[1, 2]` atom instead of a cons
chain. So collapse is per-type and applies wherever a matching value appears,
however deeply nested.
-/

#spytial (("xs", [1, 2]) : String × List Nat) with [.notationLabel (selector := "List")]

-- Expected: `Prod` atom `mk`; edge `fst` → String atom `"xs"`; edge `snd` → a
-- single `List` atom labeled `[1, 2]`.

/-! ## Collapsing `Prod` itself

The type head for a pair is `Prod`, so `.notationLabel (selector := "Prod")`
renders `(1, 2)` as one atom labeled `(1, 2)`.
-/

#spytial ((1, 2) : Nat × Nat) with [.notationLabel (selector := "Prod")]

-- Expected: a single `Prod` atom labeled `(1, 2)`, no relations.

/-! ## Combining with widget ops

`.notationLabel` coexists with ordinary layout/styling ops in the same block: the
relationalizer-side op configures the walk while the rest become the YAML. Here
the list collapses to one atom AND that atom is colored.
-/

#spytial ([1, 2, 3] : List Nat) with [
  .notationLabel (selector := "List"),
  .atomColor (selector := "List") (value := "#0066ff")
]

-- `#spytial.spec` confirms the YAML carries ONLY the widget op — the
-- `.notationLabel` op is stripped (it is not YAML):
#spytial.spec ([1, 2, 3] : List Nat) with [
  .notationLabel (selector := "List"),
  .atomColor (selector := "List") (value := "#0066ff")
]

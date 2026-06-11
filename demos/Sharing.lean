import SpytialLean

open SpytialLean

/-! # Sharing (DAG-shared subterms)

When the same subterm appears in more than one position of a value, the
relationalizer does *not* duplicate it: `walkExpr` deduplicates structurally
identical subterms by `Expr.hash`, so the two positions point at a single atom.
The result is a directed acyclic graph (DAG) rather than a tree.

To make that sharing visible, the second-and-later visit to a subterm flips a
`shared := true` flag on the already-emitted atom (see `JsonAtom.shared` and
`WalkState.markShared`). The *first* atom reached for a subterm keeps
`shared := false`; once another parent reaches the same subterm, the flag turns
on. spytial-core ignores the field today, so it is purely informational (a
consumer could, for instance, draw shared nodes with a dashed border).

Below, `sub` is built once and placed in both children of `t`, so the single
`node 7 nil nil` subtree is shared. Inspect the `#spytial.datum` output to see
`"shared": true` on the shared atom (and on the shared `nil` leaf).
-/

/-! ## A small tree -/

inductive Tree where
  | nil : Tree
  | node (key : Nat) (left : Tree) (right : Tree) : Tree
  deriving Repr

/-- A subtree built once and reused in two positions of `t`. -/
def sub : Tree := .node 7 .nil .nil

/-- `t` places `sub` in both the left and right child, so `sub` is shared. -/
def t : Tree := .node 1 sub sub

-- The diagram shows a single `node 7` atom with two incoming edges (a DAG).
#spytial t

/-! ## Inspecting the `shared` flag

The `#spytial.datum` command prints the JSON data instance. Look for the atom
corresponding to `node 7 nil nil`: it carries `"shared": true`, because it was
reached from both the `left` and the `right` edge of the root. The `nil` leaf
under it is likewise shared.
-/

#spytial.datum t

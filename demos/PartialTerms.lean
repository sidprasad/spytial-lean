import SpytialLean

/-! # Partial Terms — holes and stuck matches

Open values render structurally: an unassigned metavariable is a `?`-labeled leaf, a
hypothesis is a leaf carrying its own name, and a `match` that cannot reduce (because
its scrutinee is a hole or hypothesis) is a `match` node with a `scrutinee` edge —
instead of one opaque pretty-printed blob.

Holes keep the atom type of the slot they fill, so type-attached specs (like the tree
orientation below) lay them out exactly like ordinary nodes.
-/

inductive PTree where
  | leaf (value : Nat)
  | node (left right : PTree)

spytial_spec PTree [
  orientation left left below,
  orientation right right below
]

/-! ## Holes

A named hole renders as `?name`, an anonymous one as `?` — in tree position. `sorry`
in a data slot is just another leaf. -/

#spytial (PTree.node (PTree.node ?subtree (PTree.leaf 1)) ?_)

#spytial (PTree.node (PTree.leaf 1) sorry)

/-! ## Hypotheses

In tactic mode, a hypothesis is an opaque value — it renders as a leaf named after
itself rather than being handed to a decomposer. -/

example (t : PTree) : t = t := by
  spytial (PTree.node t (PTree.leaf 2))
  rfl

/-! ## Stuck matches

A `match` on a hypothesis (or a hole) cannot iota-reduce. It renders as a `match`
node whose `scrutinee` edge points at the value it is stuck on — composing with the
hole rendering when the scrutinee is itself a hole. -/

example (t : PTree) : t = t := by
  spytial (match t with | .leaf v => v | .node _ _ => 0)
  rfl

#spytial (match (?h : PTree) with | .leaf v => v | .node _ _ => 0)

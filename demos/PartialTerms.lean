import SpytialLean

/-! # Partial Terms — holes and stuck matches -/

inductive PTree where
  | leaf (value : Nat)
  | node (left right : PTree)

spytial_spec PTree [
  orientation left left below,
  orientation right right below
]

/-! ## Holes -/

#spytial (PTree.node (PTree.node ?subtree (PTree.leaf 1)) ?_)

#spytial (PTree.node (PTree.leaf 1) sorry)

/-! ## Hypotheses -/

example (t : PTree) : t = t := by
  spytial (PTree.node t (PTree.leaf 2))
  rfl

/-! ## Stuck matches -/

example (t : PTree) : t = t := by
  spytial (match t with | .leaf v => v | .node _ _ => 0)
  rfl

#spytial (match (?h : PTree) with | .leaf v => v | .node _ _ => 0)

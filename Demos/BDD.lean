import SpytialLean

open SpytialLean

inductive Var where | x₁ | x₂ | x₃ | x₄

inductive BDD where
  | fls
  | tru
  | node (id : Nat) (v : Var) (lo hi : BDD)

/-- `(¬x₁ ∧ ¬x₂ ∧ ¬x₃) ∨ (x₁ ∧ x₂) ∨ (x₂ ∧ x₃)` -/
def bdd : BDD :=
  .node 15 .x₁
    (.node 14 .x₂ (.node 8 .x₃ .tru .fls) (.node 4 .x₃ .fls .tru))
    (.node 3 .x₂ .fls .tru)

#print bdd

#spytial bdd with [] -- (no spec)

spytial_ops hideNoise : BDD [
  attribute id,
  attribute v,
  hideAtom Nat,
  hideAtom Var
]

#spytial bdd with [..hideNoise]

spytial_ops spatial : BDD [
  align {p, q : BDD | p != q && p.v = q.v} horizontal,
  orientation lo + hi below
]

#spytial bdd with [..hideNoise, ..spatial]

spytial_ops chrome : BDD [
  edgeStyle lo (lineStyle "#ef6c00" solid),
  edgeStyle hi (lineStyle "#2e7d32" solid),
  atomStyle {b : BDD | @:b != fls && @:b != tru} (borderStyle "#37474f"),
  atomStyle {b : BDD | @:b = fls} (borderStyle "#c62828" 3) (fillStyle "#ffcdd2"),
  atomStyle {b : BDD | @:b = tru} (borderStyle "#2e7d32" 3) (fillStyle "#e8f5e9")
]

#spytial bdd with [..hideNoise, ..spatial, ..chrome]

spytial_ops grouped : BDD [
  group {u : Var, p : BDD | @:u = @:(p.v)} nodes
]

#spytial bdd with [..hideNoise, ..spatial, ..chrome, ..grouped]

spytial_spec BDD [..hideNoise, ..spatial, ..chrome, ..grouped]

spytial_ops branches : BDD [
  orientation {p, q : BDD | q in p.lo && @:q != fls && @:q != tru} left,
  orientation {p, q : BDD | q in p.hi && @:q != fls && @:q != tru} right
]

#spytial bdd with [.., ..branches]

/-- `(¬x₁ ∧ ¬x₂ ∧ (x₃ ⊕ x₄)) ∨ (x₁ ∧ x₂ ∧ (x₃ ⊕ x₄))` -/
def shared : BDD :=
  let xor : BDD := .node 13 .x₃ (.node 5 .x₄ .fls .tru) (.node 9 .x₄ .tru .fls)
  .node 19 .x₁ (.node 14 .x₂ xor .fls) (.node 17 .x₂ .fls xor)

-- but its not always valid:
#spytial shared with [.., ..branches]

-- highlight redundant (`lo = hi`) nodes yellow
spytial_ops redundant : BDD [
  atomStyle {p : BDD | some q : BDD | q in p.lo && q in p.hi} (fillStyle "#ffe082")
]

#spytial bdd with [.., ..redundant]

/-- with redundant node 9 (`lo = hi`) -/
def unreduced : BDD :=
  .node 15 .x₁
    (.node 14 .x₂ (.node 8 .x₃ .tru .fls) (.node 4 .x₃ .fls .tru))
    (.node 3 .x₂ .fls (.node 9 .x₃ .tru .tru))

#spytial unreduced with [.., ..redundant]

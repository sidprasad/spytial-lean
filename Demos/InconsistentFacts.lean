import Demos.UnionFind

/-! # Inspecting a value with contradictory evidence

Select an inconsistent inspection to see which hypotheses Lean used to derive
`False` and what the same inspection produces with particular hypotheses omitted.
The [AVL demo](AVL.lean) shows how conflicting insertion traces affect the choice of rotation. -/

set_option linter.unusedVariables false

/-! ## Can a parent search from `x` reach `root`?

Two links are disputed independently. Each preview keeps one report per link.
Keep both links to see two solid parent arrows and a dashed edge from `x` to
`root` for the whole path through `hub`. Keep just the first and the next parent
after `hub` is unknown. Keep just the second and `hub` still points to `root`,
while the parent of `x` is unknown. -/

open UnionFindDemo in
example {Vertex : Type} (parent : Vertex → Vertex) (x hub root : Vertex)
    (isRoot : parent root = root)
    (firstLink : parent x = hub) (noFirstLink : parent x ≠ hub)
    (secondLink : parent hub = root) (noSecondLink : parent hub ≠ root) :
    Reaches parent x root := by
  spytial x observing [parent, Reaches parent] with [
    edgeStyle «Reaches parent» (lineStyle dashed),
    hideField «Reaches parent» filter: (iden + parent)]
  exact .step firstLink (.step secondLink (.refl root))

/-! ## Baseline -/

example (x : Nat) (hx : x = 3) : True := by
  spytial x
  trivial

/-! ## Two ways to inspect the same list

Lean has two conflicts about `xs`. The claim `empty` contradicts both
`singleton` and `nonempty`. Omitting `empty` gives the singleton list
`[7]`. To see the empty list, keep `empty` and omit both of the others. -/

example (xs : List Nat) (empty : xs = []) (singleton : xs = [7])
    (nonempty : xs ≠ []) : True := by
  spytial xs
  trivial

/-! ## Four omission sets, two row diagrams

One pair of hypotheses disagrees about the row and another about the column.
Inspect just `row`. Each minimal hitting set still contains one row hypothesis
and one column hypothesis. The four ways to do that give two row diagrams,
`2` and `5`. Changing only the omitted column hypothesis gives the same picture. -/

example (row col : Nat) (rowTwo : row = 2) (rowFive : row = 5)
    (colThree : col = 3) (colEight : col = 8) : True := by
  spytial row
  trivial

/-! ## A false hypothesis

The conflict uses `h`. The preview omits it and shows `3` from `hx`. -/

example (x : Nat) (hx : x = 3) (h : 1 = 2) : True := by
  spytial x
  trivial

/-! ## A false forward rule

`fyi` takes proofs, not statements: `fyi [1 = 2]` and `fyi [(sorry : 1 = 2)]` are errors.
Here simplification detects a contradiction in `r` alone. Omitting `r` retains `hx`. -/

example (x : Nat) (hx : x = 3) (r : ∀ n, n = 3 → n = 4) : True := by
  spytial x fyi [r]
  trivial

/-! ## Leaving the contradiction out

`nvm` drops the false hypothesis, so the diagram renders again. -/

example (x : Nat) (hx : x = 3) (h : 1 = 2) : True := by
  spytial x nvm [h]
  trivial

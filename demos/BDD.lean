import SpytialLean

open SpytialLean

/-! # Binary Decision Diagrams, three ways -/

inductive BDD where
  | tt
  | ff
  | node (var : Nat) (lo hi : BDD)
  deriving Repr, BEq, SpytialIdentity

def expand (f : List Bool → Bool) : Nat → List Bool → BDD
  | 0,     acc => if f acc.reverse then .tt else .ff
  | k + 1, acc =>
    .node (acc.length + 1) (expand f k (false :: acc)) (expand f k (true :: acc))

def BDD.reduce : BDD → BDD
  | .tt => .tt
  | .ff => .ff
  | .node v lo hi =>
    let lo := lo.reduce
    let hi := hi.reduce
    if lo == hi then lo else .node v lo hi

/-- `f(x₁,x₂,x₃) = x₁ ∧ x₃` — the middle variable is irrelevant, so reduction
    has something to do. -/
def fTree : BDD := expand (fun bs => bs.getD 0 false && bs.getD 2 false) 3 []

def fReduced : BDD := fTree.reduce

/- `lo - BDD->{x : BDD | @:x = tt or @:x = ff}` is the `lo` relation minus every
   pair pointing at a terminal, so the rule reads "draw the low child left of
   and below its parent, unless that child is `tt` or `ff`". Terminals have to
   be excluded because each is a single shared atom: one `tt` reached by both a
   `lo` and a `hi` edge cannot be left of one parent and right of another. -/
spytial_spec BDD [
  attribute var,
  orientation lo - BDD->{x : BDD | @:x = tt or @:x = ff} left below,
  orientation hi - BDD->{x : BDD | @:x = tt or @:x = ff} right below,
  hideAtom Nat
]

-- 1. As written: the expansion's full tree, every occurrence its own atom.
#spytial (Raw.mk fTree)

-- 2. Declared sharing: equal sub-BDDs are one atom each — one `tt`, one `ff`,
--    equal subtrees merged. The value did not change; the lens did.
#spytial fTree

-- 3. The ROBDD: `reduce` removed the redundant tests, the lens kept the
--    sharing. The picture is the paper's figure, from naive data.
#spytial fReduced

open Lean Meta in
#eval show MetaM Unit from do
  let count (e : Expr) : MetaM Nat := return (← relationalize e).atoms.size
  let asWritten ← count (← mkAppM ``Raw.mk #[mkConst ``fTree])
  let shared ← count (mkConst ``fTree)
  let robdd ← count (mkConst ``fReduced)
  unless (asWritten, shared, robdd) == (22, 12, 6) do
    throwError "BDD narrative counts drifted: got {(asWritten, shared, robdd)}, expected (22, 12, 6)"

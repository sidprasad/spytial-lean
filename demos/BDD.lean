import SpytialLean

open SpytialLean

/-! # Binary Decision Diagrams, three ways

The flagship identity demo: a **naive** Shannon expansion — no unique table,
no hash-consing, no manager — rendered at three granularities. Identity is
declared on the type (`deriving SpytialIdentity`); the renderer's identity
table plays the unique table so the program never has to.

The narrative makes two *different* moves, and says which is which:

- frame 1 → frame 2 changes the **lens** on one value (as written → declared
  sharing);
- frame 2 → frame 3 changes the **value** under one lens (`reduce` is program
  content — the ROBDD algorithm — not presentation).
-/

inductive BDD where
  | tt
  | ff
  | node (var : Nat) (lo hi : BDD)
  deriving Repr, BEq, SpytialIdentity

/-- Full Shannon expansion of `f` over `n` variables: every path spelled out,
    maximal duplication, zero cleverness. -/
def expand (f : List Bool → Bool) : Nat → List Bool → BDD
  | 0,     acc => if f acc.reverse then .tt else .ff
  | k + 1, acc =>
    .node (acc.length + 1) (expand f k (false :: acc)) (expand f k (true :: acc))

/-- Remove redundant tests (`lo = hi`) bottom-up — the reduction half of the
    ROBDD algorithm. The sharing half is the renderer's job. -/
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

/- Terminals are shared atoms, so pinning them left/right of every parent
   would over-constrain the layout — the same "subtle overconstraint" the
   Python corpus escapes by excluding terminals from orientation. Here the
   identity design *explains* the shared atom; the spec-side escape is the
   same. -/
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

/- The counts, asserted rather than narrated: 22 atoms as written (7 decision
   nodes, 7 per-node variable indices, 8 terminal occurrences), 12 under
   declared sharing (5 distinct decision nodes + their 5 index atoms + one
   `tt` + one `ff`), 6 after reduction (2 nodes, 2 indices, 2 terminals).
   Variable-index atoms stay per-node under the as-written default for `Nat` —
   merging indices across nodes would be a declaration about *indices*, not
   about BDDs, and no such declaration is made here (the diagram hides them
   into node attributes anyway). -/
open Lean Meta in
#eval show MetaM Unit from do
  let count (e : Expr) : MetaM Nat := return (← relationalize e).atoms.size
  let asWritten ← count (← mkAppM ``Raw.mk #[mkConst ``fTree])
  let shared ← count (mkConst ``fTree)
  let robdd ← count (mkConst ``fReduced)
  unless (asWritten, shared, robdd) == (22, 12, 6) do
    throwError "BDD narrative counts drifted: got {(asWritten, shared, robdd)}, expected (22, 12, 6)"

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

/-- The middle variable is irrelevant, so reduction has something to do. -/
def fTree : BDD := expand (fun bs => bs.getD 0 false && bs.getD 2 false) 3 []

def fReduced : BDD := fTree.reduce

-- Terminals are excluded from the orientations: each is one shared atom, and
-- one `tt` cannot sit left of one parent and right of another.
spytial_spec BDD [
  attribute var,
  orientation lo - BDD->{x : BDD | @:x = tt or @:x = ff} left below,
  orientation hi - BDD->{x : BDD | @:x = tt or @:x = ff} right below,
  hideAtom Nat
]

-- `Raw.mk` opts out of the identity lens: every occurrence stays its own atom.
#spytial (Raw.mk fTree)

#spytial fTree

#spytial fReduced

open Lean Meta in
#eval show MetaM Unit from do
  let count (e : Expr) : MetaM Nat := return (← relationalize e).atoms.size
  let asWritten ← count (← mkAppM ``Raw.mk #[mkConst ``fTree])
  let shared ← count (mkConst ``fTree)
  let robdd ← count (mkConst ``fReduced)
  unless (asWritten, shared, robdd) == (22, 10, 6) do
    throwError "BDD narrative counts drifted: got {(asWritten, shared, robdd)}, expected (22, 10, 6)"

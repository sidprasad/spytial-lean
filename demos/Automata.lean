import SpytialLean

open SpytialLean

/-! # Automata as state graphs

A transition function tabulates into one flat relation,
`tr : (automaton, state, symbol, state)`. Column 0 is the owner, so the
default picture fans every transition out of that one atom. Joining the owner
away leaves `(state, symbol, state)` — the automaton itself: `inferredEdge`
draws the first column to the last and folds the symbol column into the edge
label. -/

deriving instance SpytialIdentity for Fin

/-- The shape cslib uses: a labeled transition system, and a deterministic
    automaton as one with a start state. -/
structure FLTS (State Label : Type) where
  tr : State → Label → State

structure DA (State Symbol : Type) extends FLTS State Symbol where
  start : State

/- Specs compose down the parent chain, so every `DA` below draws with this
   one. `hideField tr` drops the owner fan; the symbol atoms are then edge
   labels rather than states. -/
spytial_spec FLTS [
  inferredEdge step FLTS.tr,
  hideField tr,
  hideAtom Bool
]

/-! ## `Fin` states

The `SpytialIdentity` instance is what merges the six result cells back into
the three states they came from. Without it every cell is a fresh atom, the
graph has ten states, and no edge closes a cycle. -/

/-- Counts `true` inputs mod 3. -/
def daFin : DA (Fin 3) Bool where
  tr
    | 0, false => 0
    | 0, true  => 1
    | 1, false => 1
    | 1, true  => 2
    | 2, false => 2
    | 2, true  => 0
  start := 0

-- `attribute val` would inline the state number, but `Fin` reaches the checker
-- only through `DA`'s type parameter, so that name does not check here.
#spytial daFin

/-! ## Named states

The same automaton over an enumerated state type: the constructor names are
the labels, so nothing has to be inlined. -/

inductive St where | s0 | s1 | s2
  deriving DecidableEq, SpytialIdentity

def daSt : DA St Bool where
  tr
    | .s0, false => .s0
    | .s0, true  => .s1
    | .s1, false => .s1
    | .s1, true  => .s2
    | .s2, false => .s2
    | .s2, true  => .s0
  start := .s0

#spytial daSt

/-! ## Nondeterminism

`Tr : State → Symbol → State → Prop` is a relation, not a function: its table
has no result column and carries a tuple exactly where the proposition decides
true, including two targets on one symbol. `start` is a predicate over states,
which is what `Set State` unfolds to (Mathlib is not on this dependency path);
its memberships draw as automaton→state edges with no directive. -/

structure NA (State Symbol : Type) where
  Tr : State → Symbol → State → Prop
  start : State → Prop

spytial_spec NA [
  inferredEdge step NA.Tr,
  hideField Tr,
  hideAtom Bool
]

def naSt : NA St Bool where
  Tr q a q' :=
    (q = .s0 ∧ a = false ∧ q' = .s0) ∨
    (q = .s0 ∧ a = true  ∧ q' = .s1) ∨
    (q = .s0 ∧ a = true  ∧ q' = .s2) ∨
    (q = .s1 ∧ a = false ∧ q' = .s2)
  start q := q = .s0 ∨ q = .s1

#spytial naSt

open Lean Meta in
#eval show MetaM Unit from do
  let stateAtoms (value : Name) (ty : String) : MetaM Nat := do
    return ((← relationalize (mkConst value)).atoms.filter (·.type == ty)).size
  let counts := (← stateAtoms ``daFin "Fin", ← stateAtoms ``daSt "St",
                 ← stateAtoms ``naSt "St")
  unless counts == (3, 3, 3) do
    throwError "state atoms drifted: got {counts}, expected (3, 3, 3)"

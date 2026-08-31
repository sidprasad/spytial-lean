import SpytialLean

open SpytialLean

/-! # Automata as state graphs -/

deriving instance SpytialIdentity for Fin

structure FLTS (State Label : Type) where
  tr : State → Label → State

structure DA (State Symbol : Type) extends FLTS State Symbol where
  start : State

-- Specs compose down `extends`, so every `DA` below draws with this one.
spytial_spec FLTS [
  inferredEdge step FLTS.tr,
  hideField tr,
  hideAtom Bool
]

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

#spytial daFin

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

/-- `Tr` tabulates a tuple wherever it decides true. -/
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

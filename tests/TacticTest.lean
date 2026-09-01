import SpytialLean

open SpytialLean

/-! # Tactic-position smoke tests

Command coverage proves nothing about the tactics: `#spytial`* atoms tokenize
via the symbol path (`#` cannot begin an identifier), while the tactics are
subject to identifier lexing — see `spytialProofKw`. These tests elaborate
every tactic surface headlessly; a parse or elaboration failure fails the
build. -/

inductive TEven : Nat → Prop where
  | zero : TEven 0
  | add_two : TEven n → TEven (n + 2)

theorem teven_four : TEven 4 := .add_two (.add_two .zero)

-- data tactic on a global
example : True := by
  spytial [1, 2, 3]
  trivial

-- data tactic on a local hypothesis (widget payloads don't count as
-- references, so the unused-variable linter would fire spuriously)
set_option linter.unusedVariables false in
example (xs : List Nat) : True := by
  spytial xs
  trivial

-- data tactic with an inline spec
example : True := by
  spytial [1, 2, 3] with [hideAtom Nat]
  trivial

-- proof tactic on a global
example : True := by
  spytial.proof teven_four
  trivial

-- proof tactic on a local hypothesis
set_option linter.unusedVariables false in
example (h : TEven 4) : True := by
  spytial.proof h
  trivial

-- proof tactic with an inline spec
example : True := by
  spytial.proof teven_four with [hideAtom Nat]
  trivial

-- the tactics see hypotheses introduced by earlier tactics (withMainContext)
set_option linter.unusedVariables false in
example : ∀ n : Nat, True := by
  intro n
  spytial n
  trivial

set_option linter.unusedVariables false in
example : ∀ h : TEven 4, True := by
  intro h
  spytial.proof h
  trivial

-- context knowledge: an equation refines the subject in place
set_option linter.unusedVariables false in
example (xs : List Nat) (h : xs = [1]) : True := by
  spytial xs
  trivial

-- context knowledge after intro
set_option linter.unusedVariables false in
example : ∀ a b : Nat, a < b → True := by
  intro a b h
  spytial a
  trivial

-- ops elaborate against the merged scope: subject type plus positive fact
-- vocabulary
set_option linter.unusedVariables false in
example (a b : Nat) (h : a < b) : True := by
  spytial a with [edgeStyle lt (lineStyle "blue")]
  trivial

-- ∧ splits: both halves draw
set_option linter.unusedVariables false in
example (a b : Nat) (h : a < b ∧ b < a) : True := by
  spytial a
  trivial

-- `fyi` supplies a proved rule: symmetry proves the reverse arrow
set_option linter.unusedVariables false in
example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (hs : ∀ a b, R a b → R b a) : True := by
  spytial x fyi [hs]
  trivial

set_option linter.unusedVariables false in
example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (hs : ∀ a b, R a b → R b a) : True := by
  spytial.datum x fyi [hs]
  trivial

-- disjunctions are accepted but deliberately contribute no knowledge
set_option linter.unusedVariables false in
example (n : Nat) (h : n = 1 ∨ n = 2) (h2 : n ≠ 1) : True := by
  spytial n
  trivial

-- existentials: the witness is a hole
set_option linter.unusedVariables false in
example {R : Nat → Nat → Prop} (a : Nat) (h : ∃ b, R a b) : True := by
  spytial a
  trivial

set_option linter.unusedVariables false in
example (xs : List Nat) (h : ∃ y, xs = [y, y]) : True := by
  spytial xs
  trivial

-- observations apply named data functions over the represented active domain
set_option linter.unusedVariables false in
/--
info: {"relations":
 [{"types": ["Nat", "Nat"],
   "tuples": [{"types": ["Nat", "Nat"], "atoms": ["atom_0", "atom_1"]}],
   "name": "measure",
   "id": "measure"}],
 "atoms":
 [{"type": "Nat", "label": "x", "id": "atom_0"},
  {"type": "Nat", "label": "?₁", "id": "atom_1"}]}
-/
#guard_msgs in
example (measure : Nat → Nat) (x : Nat) : True := by
  spytial.datum x observing [measure]
  trivial

def twice (x : Nat) : Nat := x * 2

/--
info: {"relations":
 [{"types": ["Nat", "Nat"],
   "tuples": [{"types": ["Nat", "Nat"], "atoms": ["atom_0", "atom_1"]}],
   "name": "twice",
   "id": "twice"}],
 "atoms":
 [{"type": "Nat", "label": "3", "id": "atom_0"},
  {"type": "Nat", "label": "6", "id": "atom_1"}]}
-/
#guard_msgs in
#spytial.datum 3 observing [twice]

#spytial 3 observing [twice] with [attribute twice]

-- The observer's domain, not the selected root's type, determines where it
-- applies. `twice` observes the Nat inside this pair without having to accept
-- the pair itself.
set_option linter.unusedVariables false in
example (n : Nat) (flag : Bool) : True := by
  spytial (n, flag) observing [twice]
  trivial

-- Only the requested observation enters the layout vocabulary, not the
-- arithmetic used to implement it. This also checks observing inside a def.
def observedNext (n : Nat) : Nat := n + 1

run_elab
  Lean.Meta.withLocalDeclD `n (Lean.mkConst ``Nat) fun _ => do
    let .ok op := Lean.Parser.runParserCategory (← Lean.getEnv) `spytial_op "attribute observedNext"
      | throwError "could not parse observation layout"
    discard <| spytialPayloadProps (Lean.mkIdent `n)
      (some #[⟨op⟩]) {} #[Lean.mkIdent ``observedNext]

def inspectNext (n : Nat) : Nat := by
  spytial n observing [observedNext] with [attribute observedNext]
  exact n + 1

/--
info: {"relations":
 [{"types": ["Nat", "Nat"],
   "tuples": [{"types": ["Nat", "Nat"], "atoms": ["atom_0", "atom_1"]}],
   "name": "twice",
   "id": "twice"}],
 "atoms":
 [{"type": "Nat", "label": "3", "id": "atom_0"},
  {"type": "Nat", "label": "6", "id": "atom_1"}]}
-/
#guard_msgs in
example : True := by
  spytial.datum 3 observing [twice]
  trivial

-- observation relations are available to the ordinary use-site specification
set_option linter.unusedVariables false in
example (measure : Nat → Nat) (x : Nat) : True := by
  spytial x observing [measure] with [attribute measure]
  trivial

set_option linter.unusedVariables false in
example {R : Nat → Nat → Prop} (measure : Nat → Nat) (x y : Nat)
    (h : R x y) (symmetric : ∀ a b, R a b → R b a) : True := by
  spytial x observing [measure] fyi [symmetric] with [attribute measure]
  trivial

-- predicates remain proof-backed facts rather than data observations
set_option linter.unusedVariables false in
/--
error: 'observing' expects a data-returning function, not a predicate
-/
#guard_msgs in
example (P : Nat → Prop) (x : Nat) : True := by
  spytial x observing [P]
  trivial

def Positive (x : Nat) : Prop := 0 < x

/--
error: 'observing' expects a data-returning function, not a predicate
-/
#guard_msgs in
#spytial 3 observing [Positive]

-- ordinary negative or unsupported knowledge is silent
set_option linter.unusedVariables false in
example (n : Nat) (h : n ≠ 0) : True := by
  spytial n
  trivial

-- the caller can supply an explicit IYKYK forward rule
set_option linter.unusedVariables false in
example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (symmetric : ∀ a b, R a b → R b a) : True := by
  spytial x fyi [symmetric]
  trivial

set_option linter.unusedVariables false in
example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (symmetric : ∀ a b, R a b → R b a) : True := by
  spytial x fyi [symmetric] with [edgeStyle R (lineStyle "blue")]
  trivial

-- all three clauses in order
set_option linter.unusedVariables false in
example {R : Nat → Nat → Prop} (measure : Nat → Nat) (x y : Nat)
    (h : R x y) (symmetric : ∀ a b, R a b → R b a) : True := by
  spytial x observing [measure] fyi [symmetric] with [attribute measure]
  trivial

-- datum tactic, with and without an explicit rule
set_option linter.unusedVariables false in
example (a b : Nat) (h : a < b) : True := by
  spytial.datum a
  trivial

set_option linter.unusedVariables false in
example {α : Type} (R : α → α → Prop) (x y : α)
    (h : R x y) (symmetric : ∀ a b, R a b → R b a) : True := by
  spytial.datum x fyi [symmetric]
  trivial

-- a use-site `with [...]` can splice the type's attached spec
structure SpliceBox where
  contents : Nat

spytial_spec SpliceBox [hideAtom Nat]

set_option linter.unusedVariables false in
example (b : SpliceBox) : True := by
  spytial b with [..]
  trivial

-- `fyi` rejects a term that proves nothing
set_option linter.unusedVariables false in
/--
error: 'fyi' expects a hypothesis: a proof of a Prop-typed statement, but this term has type Nat
-/
#guard_msgs in
example (x n : Nat) (h : x < n) : True := by
  spytial.datum x fyi [n]
  trivial

-- a witness occurring inside the refined subject is the one shared `?₁` atom
set_option linter.unusedVariables false in
/--
info: {"relations":
 [{"types": ["List", "List"],
   "tuples": [{"types": ["List", "List"], "atoms": ["atom_1", "atom_2"]}],
   "name": "=",
   "id": "="},
  {"types": ["List", "Nat"],
   "tuples":
   [{"types": ["List", "Nat"], "atoms": ["atom_2", "atom_0"]},
    {"types": ["List", "Nat"], "atoms": ["atom_3", "atom_0"]}],
   "name": "head",
   "id": "head"},
  {"types": ["List", "List"],
   "tuples":
   [{"types": ["List", "List"], "atoms": ["atom_3", "atom_4"]},
    {"types": ["List", "List"], "atoms": ["atom_2", "atom_3"]}],
   "name": "tail",
   "id": "tail"}],
 "atoms":
 [{"type": "Nat", "label": "?₁", "id": "atom_0"},
  {"type": "List", "label": "xs", "id": "atom_1"},
  {"type": "List", "label": "cons", "id": "atom_2"},
  {"type": "List", "label": "cons", "id": "atom_3"},
  {"type": "List", "label": "nil", "id": "atom_4"}]}
-/
#guard_msgs in
example (xs : List Nat) (h : ∃ y, xs = [y, y]) : True := by
  spytial.datum xs
  trivial

-- witness labels and generated application labels share one counter: `?₁` and
-- `?₂`, never `?₁` twice
set_option linter.unusedVariables false in
/--
info: {"relations":
 [{"types": ["α", "α"],
   "tuples": [{"types": ["α", "α"], "atoms": ["atom_1", "atom_2"]}],
   "name": "next",
   "id": "next"},
  {"types": ["α"],
   "tuples": [{"types": ["α"], "atoms": ["atom_2"]}],
   "name": "Reach",
   "id": "Reach"},
  {"types": ["α", "α"],
   "tuples": [{"types": ["α", "α"], "atoms": ["atom_1", "atom_0"]}],
   "name": "edge",
   "id": "edge"}],
 "atoms":
 [{"type": "α", "label": "?₁", "id": "atom_0"},
  {"type": "α", "label": "s", "id": "atom_1"},
  {"type": "α", "label": "?₂", "id": "atom_2"}]}
-/
#guard_msgs in
example {α : Type} (edge : α → α → Prop) (Reach : α → Prop) (next : α → α) (s : α)
    (route : ∃ u, edge s u) (h : Reach (next s)) : True := by
  spytial.datum s
  trivial

-- two predicates sharing a short name cannot corrupt one relation: the
-- colliding arity warns and stays undrawn
namespace ArityFoo
inductive Adj : Nat → Nat → Prop
end ArityFoo
namespace ArityBar
inductive Adj : Nat → Nat → Nat → Prop
end ArityBar

set_option linter.unusedVariables false in
/--
warning: spytial: 'Adj' names relations of arity 2 and 3; the second is not drawn
---
info: {"relations":
 [{"types": ["Nat", "Nat"],
   "tuples": [{"types": ["Nat", "Nat"], "atoms": ["atom_0", "atom_1"]}],
   "name": "Adj",
   "id": "Adj"}],
 "atoms":
 [{"type": "Nat", "label": "x", "id": "atom_0"},
  {"type": "Nat", "label": "y", "id": "atom_1"}]}
-/
#guard_msgs in
example (x y z : Nat) (h₁ : ArityFoo.Adj x y) (h₂ : ArityBar.Adj x y z) : True := by
  spytial.datum x
  trivial

-- the simp engine splits a same-constructor equation into field equalities,
-- so the refinement draws `a` as `c`
set_option linter.unusedVariables false in
/--
info: {"relations": [], "atoms": [{"type": "Nat", "label": "c", "id": "atom_0"}]}
-/
#guard_msgs in
example (a b c d : Nat) (h : (a, b) = (c, d)) : True := by
  spytial.datum a
  trivial

-- the tactic tabulates a closed enumerable function field exactly as
-- `#spytial` does
inductive TabQ where
  | q0 | q1 | q2
  deriving Repr

structure TabStep where
  step : TabQ → TabQ

instance : SpytialIdentity TabStep := .asWritten

def tabStepVal : TabStep :=
  ⟨fun q => match q with | .q0 => .q1 | .q1 => .q2 | .q2 => .q0⟩

/--
info: {"relations":
 [{"types": ["TabStep", "TabQ", "TabQ"],
   "tuples":
   [{"types": ["TabStep", "TabQ", "TabQ"],
     "atoms": ["atom_0", "atom_1", "atom_2"]},
    {"types": ["TabStep", "TabQ", "TabQ"],
     "atoms": ["atom_0", "atom_2", "atom_3"]},
    {"types": ["TabStep", "TabQ", "TabQ"],
     "atoms": ["atom_0", "atom_3", "atom_1"]}],
   "name": "step",
   "id": "step"}],
 "atoms":
 [{"type": "TabStep", "label": "mk", "id": "atom_0"},
  {"type": "TabQ", "label": "q0", "id": "atom_1"},
  {"type": "TabQ", "label": "q1", "id": "atom_2"},
  {"type": "TabQ", "label": "q2", "id": "atom_3"}]}
-/
#guard_msgs in
#spytial.datum tabStepVal

set_option linter.unusedVariables false in
/--
info: {"relations":
 [{"types": ["TabStep", "TabQ", "TabQ"],
   "tuples":
   [{"types": ["TabStep", "TabQ", "TabQ"],
     "atoms": ["atom_0", "atom_1", "atom_2"]},
    {"types": ["TabStep", "TabQ", "TabQ"],
     "atoms": ["atom_0", "atom_2", "atom_3"]},
    {"types": ["TabStep", "TabQ", "TabQ"],
     "atoms": ["atom_0", "atom_3", "atom_1"]}],
   "name": "step",
   "id": "step"}],
 "atoms":
 [{"type": "TabStep", "label": "mk", "id": "atom_0"},
  {"type": "TabQ", "label": "q0", "id": "atom_1"},
  {"type": "TabQ", "label": "q1", "id": "atom_2"},
  {"type": "TabQ", "label": "q2", "id": "atom_3"}]}
-/
#guard_msgs in
example : True := by
  spytial.datum tabStepVal
  trivial

/-! ## Raw Lean selectors in tactic position

The knowledge walk keeps the term behind each atom. These tests pin closed
evaluation and the whole-value restriction; KnowledgeSelectorTest also covers
predicate resolution from evidence about symbolic terms. -/

section WireSpec
open Lean Meta Elab Tactic

/-- Tactic analog of LeanSelectorTest's `#wire_spec`: print the `cndSpec` the
    widget receives, so a golden pins what a raw Lean selector resolved to in
    tactic mode. -/
syntax (name := spytialWireSpecTac) "spytial_wire_spec " term
  (" with " "[" spytial_op,*,? "]")? : tactic

syntax (name := spytialProgrammaticBaselineTac) "spytial_programmatic_baseline " term : tactic

@[tactic spytialWireSpecTac]
def elabSpytialWireSpecTac : Tactic := fun stx => do
  let ops? := if stx[2].getNumArgs == 0 then none
    else some (stx[2][2].getSepArgs.map fun op => (⟨op⟩ : TSyntax `spytial_op))
  let props ← withMainContext do
    let subject ← Term.elabTerm stx[1] none
    Term.synthesizeSyntheticMVarsNoPostponing
    Prod.fst <$> spytialInContextProps (← instantiateMVars subject) ops?
  logInfo (match props.getObjValD "cndSpec" with
    | .str spec => spec
    | j => toString j)

/-- Exercise the public API with an observation and no explicit hypotheses. -/
@[tactic spytialProgrammaticBaselineTac]
def elabSpytialProgrammaticBaselineTac : Tactic := fun stx => do
  withMainContext do
    let subject ← Term.elabTerm stx[1] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let subject ← instantiateMVars subject
    discard <| spytialInContextProps subject none {} #[] #[subject]

end WireSpec

-- The programmatic API keeps simp enabled when its caller supplies no hypotheses.
set_option linter.unusedVariables false in
/-- error: spytial: IYKYK found an inconsistent context -/
#guard_msgs in
example (h : (some 1 : Option Nat) = none) : True := by
  spytial_programmatic_baseline 0

-- a predicate runs on the values the refinement established
set_option linter.unusedVariables false in
set_option spytial.source false in
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_1"}}]} -/
#guard_msgs in
example (xs : List Nat) (h : xs = [1]) : True := by
  spytial_wire_spec xs with [hideAtom lean (fun n : Nat => n == 1)]
  trivial

-- the real tactic surface accepts the same selector
set_option linter.unusedVariables false in
example (xs : List Nat) (h : xs = [1]) : True := by
  spytial xs with [hideAtom lean (fun n : Nat => n == 1)]
  trivial

-- The inequality alone establishes neither endpoint to be zero.
set_option linter.unusedVariables false in
set_option spytial.source false in
/-- info: {"constraints": [{"hideAtom": {"selector": "none"}}]} -/
#guard_msgs in
example (a b : Nat) (h : a < b) : True := by
  spytial_wire_spec a with [hideAtom lean (fun n : Nat => n == 0)]
  trivial

-- a `Spytial.Sel` receives the refined subject as the whole value
def listElems : Spytial.Sel (List Nat) Nat := ⟨fun xs => xs⟩

set_option linter.unusedVariables false in
set_option spytial.source false in
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_1"}}]} -/
#guard_msgs in
example (xs : List Nat) (h : xs = [1]) : True := by
  spytial_wire_spec xs with [hideAtom lean (listElems)]
  trivial

-- … and is refused when the context does not determine the value
set_option linter.unusedVariables false in
/--
error: a `Spytial.Sel` runs on the whole value being drawn, but the context does not determine that value; a predicate selects among the individually known values instead
-/
#guard_msgs in
example (xs : List Nat) : True := by
  spytial xs with [hideAtom lean (listElems)]
  trivial

-- an attached spec's lean selector resolves in tactic mode too
structure SelCrate where
  contents : Nat

-- stamp off at declaration: the stored stamp would put this file's own line
-- number in the golden
set_option spytial.source false in
spytial_spec SelCrate [hideAtom lean (fun n : Nat => n == 5)]

set_option linter.unusedVariables false in
set_option spytial.source false in
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_1"}}]} -/
#guard_msgs in
example (c : SelCrate) (h : c = ⟨5⟩) : True := by
  spytial_wire_spec c
  trivial

module

public import Lean.Elab.Command
public meta import SpytialLean.Attr
public meta import SpytialLean.Command

open SpytialLean Lean Elab Command

/-! # Tests for raw Lean selectors

`lean (…)` selects by running an ordinary Lean function over the values the walk
produced. Goldens pin the tuples it resolves to, since those *are* the
observable behaviour; the negative tests pin one diagnostic per rejection
class. -/

/-! ## Fixtures -/

public inductive LHue where
  | red | black
  deriving DecidableEq, BEq

public inductive LRB where
  | nil : LRB
  | node (color : LHue) (key : Nat) (left right : LRB) : LRB
  deriving BEq

public def LRB.isBlack : LRB → Bool
  | .node .black .. => true
  | _ => false

public def LRB.lt : LRB → LRB
  | .node _ _ l _ => l
  | .nil => .nil

public def LRB.kids : LRB → Array LRB
  | .nil => #[]
  | .node _ _ l r => #[l, r]

public def LRB.inner : LRB → Option LRB
  | .node _ _ l@(.node ..) _ => some l
  | _ => none

/-- Root black, one nil child on each side. Atoms: 0 node, 1 black, 2 key,
    3 nil, 4 nil. -/
public def lSmall : LRB := .node .black 1 .nil .nil

/-- Root red over a black node; the black one is *not* the root, so an
    `isBlack` selector must pick an interior atom. Atoms: 0 node, 1 red, 2 key,
    3 node, 4 black, 5 key, 6 nil, 7 nil, 8 nil. -/
public def lBig : LRB := .node .red 1 (.node .black 2 .nil .nil) .nil

public section

/-- Dump the `cndSpec` the widget actually receives, so the deferred
    resolution of an attached spec is what gets tested — not a re-render. -/
syntax (name := wireSpecCmd) "#wire_spec " term : command

end

@[command_elab wireSpecCmd]
public meta def elabWireSpec : CommandElab := fun
  | `(#wire_spec $t:term) => do
    let props ← liftTermElabM <| spytialPayloadProps t
    logInfo m!"{props.getObjValD "cndSpec"}"
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Arity 1

A predicate resolves to the atoms it selects — the extensional form
spytial-core resolves by atom id. -/

/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_3 + `atom_4"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun n : LRB => n matches .nil)]

-- A `Prop`-valued predicate goes through `Decidable`, not compiled `Bool`.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_1"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun c : LHue => c = LHue.black)]

-- The argument type fixes the sig the column ranges over, so scalar atoms are
-- reachable like any other.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_2"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun k : Nat => k > 0)]

-- A `def` reads the same as a lambda.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (LRB.isBlack)]

-- Resolution happens before lowering, so a resolved selector composes with the
-- relational DSL like any other expression.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_3 + `atom_4 + LHue"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun n : LRB => n matches .nil) + LHue]

-- An empty selection is `none`, not an empty union.
/-- info: {"constraints": [{"hideAtom": {"selector": "none"}}]} -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun _ : LHue => false)]

-- A function that cannot be decided selects nothing rather than guessing:
-- `decideProp?` returns `none` and the atom is skipped.
/-- info: {"constraints": [{"hideAtom": {"selector": "none"}}]} -/
#guard_msgs in
#spytial.spec lSmall with
  [hideAtom lean (fun n : LRB => ∀ m : Nat, n matches .nil ∧ m > 0)]

/-! ## Arity n

A tuple lowers to a product, and the tuples to a union. A column past the
arguments is *computed*: the function returns a value, and the column is every
atom holding it. Selection is by value — a value held by several atoms selects
all of them. -/

-- `lt` of the interior node is `.nil`, and three atoms hold `.nil`, so the
-- interior node relates to all three — as does each `.nil` via `lt`'s own
-- fixpoint. Equal values cannot be told apart; position is the relational
-- language's job.
/--
info: {"constraints":
 [{"orientation":
   {"selector":
    "`atom_0->`atom_3 + `atom_3->`atom_6 + `atom_3->`atom_7 + `atom_3->`atom_8 + `atom_6->`atom_6 + `atom_6->`atom_7 + `atom_6->`atom_8 + `atom_7->`atom_6 + `atom_7->`atom_7 + `atom_7->`atom_8 + `atom_8->`atom_6 + `atom_8->`atom_7 + `atom_8->`atom_8",
    "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lBig with [orientation lean (LRB.lt) below]

-- An `Array`/`List`/`Option` codomain emits tuples per element. Both of the
-- interior node's children are `.nil` — one value — so its `kids` reach every
-- `.nil` atom once (duplicate tuples collapse), and so do the root's.
/--
info: {"directives":
 [{"inferredEdge":
   {"selector":
    "`atom_0->`atom_3 + `atom_0->`atom_6 + `atom_0->`atom_7 + `atom_0->`atom_8 + `atom_3->`atom_6 + `atom_3->`atom_7 + `atom_3->`atom_8",
    "name": "kids"}}]}
-/
#guard_msgs in
#spytial.spec lBig with [inferredEdge kids lean (LRB.kids)]

/--
info: {"constraints":
 [{"orientation": {"selector": "`atom_0->`atom_3", "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lBig with [orientation lean (LRB.inner) below]

-- Arity 2 as a binary predicate: the product of the two columns, one decision
-- per point. It selects exactly what `lean (LRB.lt)` above selects — the two
-- forms mean the same thing, and differ only in cost: the predicate decides
-- every pair, the computed column makes one call per atom.
/--
info: {"constraints":
 [{"orientation":
   {"selector":
    "`atom_0->`atom_3 + `atom_3->`atom_6 + `atom_3->`atom_7 + `atom_3->`atom_8 + `atom_6->`atom_6 + `atom_6->`atom_7 + `atom_6->`atom_8 + `atom_7->`atom_6 + `atom_7->`atom_7 + `atom_7->`atom_8 + `atom_8->`atom_6 + `atom_8->`atom_7 + `atom_8->`atom_8",
    "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lBig with [orientation lean (fun p c : LRB => p.lt == c) below]

-- Arity 3.
/--
info: {"directives":
 [{"inferredEdge": {"selector": "`atom_0->`atom_4->`atom_5", "name": "tri"}}]}
-/
#guard_msgs in
#spytial.spec lBig with
  [inferredEdge tri lean (fun (n : LRB) (h : LHue) (k : Nat) =>
     n matches .node .red _ _ _ && h == .black && k > 1)]

-- The arity reaches the op's position check, so a mismatch is still an error.
/-- error: this position selects atoms (arity 1), but the selector has arity 2 -/
#guard_msgs in
#spytial.spec lBig with [hideAtom lean (LRB.lt)]

-- The enumerated product is capped, and the error names the cheaper shape.
/--
error: raw Lean selector ranges over 4225 points (65 × 65), over the limit of 4096; a function-valued selector computes its last column instead of enumerating it
-/
#guard_msgs in
#spytial.spec (List.range 65) with [orientation lean (fun a b : Nat => a == b) below]

/-! ## Deferred resolution

An attached spec is elaborated with no value in sight and stored structurally;
the function runs at *use*, once per value. -/

spytial_spec LRB [
  hideAtom lean (fun n : LRB => n matches .nil),
  atomStyle lean (LRB.isBlack) (borderStyle "black")
]

/-- info: "{\"directives\":\n [{\"atomStyle\": {\"selector\": \"`atom_0\", \"borderStyle\": {\"color\": \"black\"}}}],\n \"constraints\": [{\"hideAtom\": {\"selector\": \"`atom_3 + `atom_4\"}}]}" -/
#guard_msgs in
#wire_spec lSmall

-- Same stored spec, different value: `isBlack` now picks the interior node,
-- and there are three nils.
/-- info: "{\"directives\":\n [{\"atomStyle\": {\"selector\": \"`atom_3\", \"borderStyle\": {\"color\": \"black\"}}}],\n \"constraints\": [{\"hideAtom\": {\"selector\": \"`atom_6 + `atom_7 + `atom_8\"}}]}" -/
#guard_msgs in
#wire_spec lBig

/-! ## Rejections -/

/-- error: a raw Lean selector must be a function over the walked types, but this term has type Nat -/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (42)]

-- A type the walk cannot reach can never fill its column; in a strict scope
-- that is worth naming rather than silently rendering as empty.
/--
warning: 'Float' is not among the types reachable from 'LRB', so this selector cannot match anything
---
info: {"constraints": [{"hideAtom": {"selector": "none"}}]}
-/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun _ : Float => true)]

-- Lean's own error, and only Lean's error: no follow-on complaint about the
-- holes in the recovery term.
/--
error: Invalid field `nosuchfield`: The environment does not contain `LRB.nosuchfield`, so it is not possible to project the field `nosuchfield` from an expression
  n
of type `LRB`
---
info: {"constraints": [{"hideAtom": {"selector": "none"}}]}
-/
#guard_msgs in
#spytial.spec lSmall with [hideAtom lean (fun n : LRB => n.nosuchfield)]

/-! ## `lean` is not a reserved word

The rule is non-reserved and needs its parenthesis, so a relation actually
named `lean` still reads as an ordinary identifier. -/

public inductive LKw where
  | mk (lean : Nat) (rest : LKw)
  | stop

public def lKw : LKw := .mk 1 .stop

/-- info: {"directives": [{"hideField": {"field": "lean"}}]} -/
#guard_msgs in
#spytial.spec lKw with [hideField lean]

/--
info: {"constraints":
 [{"orientation": {"selector": "lean", "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec lKw with [orientation lean below]

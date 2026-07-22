module

public import Lean.Elab.Command
public meta import SpytialLean.Attr
meta import SpytialLean.Command

open SpytialLean Lean Elab Command

/-! # Tests for the embedded selector DSL

Headless, widget-free. Golden tests pin the SGQ lowering of every selector
shape the corpus uses (`#guard_msgs` on the YAML debug command and on a
spec-storage dump); negative tests pin one diagnostic per checker error class.
Run with `lake build SpytialTests`.
-/

/-! ## Fixtures -/

/-- Monomorphic, so its scope is strict: unknown names are errors. -/
public inductive SBDD where
  | tt
  | ff
  | node (v : String) (lo hi : SBDD)

public def sExample : SBDD := .node "x" .tt .ff

/-- Color + keyed nodes, for ctor-label comparisons through a field. -/
public inductive SColor where
  | red | black

public inductive SRB where
  | nil
  | node (color : SColor) (key : Nat) (left right : SRB)

public def sRB : SRB := .node .red 1 .nil .nil

/-- Polymorphic, so its scope is lenient: unknown names warn, resolved types
    pass silently. -/
public inductive STree (α : Type) where
  | leaf (value : α)
  | node (left right : STree α)

public def sTree : STree Nat := .node (.leaf 1) (.leaf 2)

public section

/-- Dump the stored spec of a type as YAML (tests attach + storage + lowering). -/
syntax (name := specYamlCmd) "#spec_yaml " ident : command

end

@[command_elab specYamlCmd]
public meta def elabSpecYaml : CommandElab := fun
  | `(#spec_yaml $id:ident) => do
    let n ← liftTermElabM (realizeGlobalConstNoOverloadWithInfo id)
    match getSpytialSpec? (← getEnv) n with
    | some spec => logInfo spec.toYaml
    | none => throwError "no spec attached to '{n}'"
  | _ => throwUnsupportedSyntax

/-! ## Golden lowering — the full BDD-shaped op battery -/

/--
info: constraints:
  - orientation: {selector: "{x, y : SBDD | x->y in lo + hi}", directions: [below]}
  - orientation: {selector: "lo - SBDD->{b : SBDD | @:b = tt} - SBDD->{b : SBDD | @:b = ff}", directions: [left]}
  - align: {selector: "{x, y : SBDD | x != y and x.v = y.v}", direction: horizontal}
  - group: {selector: "{vr : String, y : SBDD | @:vr = @:(y.v)}", name: "nodes"}
  - hideAtom: {selector: "String"}
  - size: {selector: "SBDD", width: 120, height: 80}
  - cyclic: {selector: "{x, y : SBDD | x->y in lo}", direction: counterclockwise}
directives:
  - edgeColor: {field: "lo", value: "orange", style: dashed}
  - atomColor: {selector: "{x : SBDD | @:x = ff}", value: "red"}
  - attribute: {field: "v"}
  - inferredEdge: {name: "shortcut", selector: "lo.hi", color: "#123456", style: dotted}
  - icon: {selector: "{x : SBDD | @:x = tt}", path: "tt.png", showLabels: true}
  - tag: {toTag: "SBDD", name: "kind", value: "bdd"}
  - flag: hideDisconnected
  - hideField: {field: "hi"}
  - atomColor: {selector: "raw & unchecked \"quoted\"", value: "green"}
-/
#guard_msgs in
#spytial.spec sExample with [
  orientation {x, y : SBDD | x->y in (lo + hi)} below,
  orientation lo - SBDD->{b : SBDD | @:b = tt} - SBDD->{b : SBDD | @:b = ff} left,
  align {x, y : SBDD | (x != y) && (x.v) = (y.v)} horizontal,
  group {vr : String, y : SBDD | @:vr = @:(y.v)} nodes,
  edgeColor lo "orange" dashed,
  atomColor {x : SBDD | @:x = ff} "red",
  attribute v,
  hideAtom String,
  size SBDD 120 80,
  cyclic {x, y : SBDD | x->y in lo} counterclockwise,
  inferredEdge shortcut lo.hi "#123456" dotted,
  icon {x : SBDD | @:x = tt} "tt.png" labels,
  tag SBDD "kind" "bdd",
  flag hideDisconnected,
  hideField hi,
  atomColor "raw & unchecked \"quoted\"" "green"
]

/-! ## Golden storage — `spytial_spec` attaches the structured spec -/

spytial_spec SRB [
  orientation left - SRB->{x : SRB | @:x = nil} left below,
  orientation right - SRB->{x : SRB | @:x = nil} right below,
  hideAtom SColor + Nat,
  atomColor {x : SRB | @:(x.color) = red} "red",
  attribute key
]

/--
info: constraints:
  - orientation: {selector: "left - SRB->{x : SRB | @:x = nil}", directions: [left, below]}
  - orientation: {selector: "right - SRB->{x : SRB | @:x = nil}", directions: [right, below]}
  - hideAtom: {selector: "SColor + Nat"}
directives:
  - atomColor: {selector: "{x : SRB | @:(x.color) = red}", value: "red"}
  - attribute: {field: "key"}
-/
#guard_msgs in
#spec_yaml SRB

/-! ## Closure operators and joins -/

/--
info: constraints:
  - orientation: {selector: "^lo", directions: [below]}
  - orientation: {selector: "~hi", directions: [above]}
  - orientation: {selector: "lo & iden", directions: [below]}
  - hideAtom: {selector: "SBDD.lo"}
-/
#guard_msgs in
#spytial.spec sExample with [
  orientation ^lo below,
  orientation ~hi above,
  orientation lo & iden below,
  hideAtom SBDD . lo
]

/-! ## Lenient (polymorphic) scope: resolved element types pass silently,
    unresolvable names warn and pass through -/

/--
info: constraints:
  - orientation: {selector: "left", directions: [left, below]}
  - hideAtom: {selector: "Nat"}
-/
#guard_msgs in
#spytial.spec sTree with [
  orientation left left below,
  hideAtom Nat
]

/--
warning: unknown name 'lft' (did you mean 'left'?) — the vocabulary of 'STree' is open (a custom relationalizer, type parameter, or function field makes it unpredictable), so the name passes through unchecked
---
info: constraints:
  - orientation: {selector: "lft", directions: [below]}
-/
#guard_msgs in
#spytial.spec sTree with [
  orientation lft below
]

/-! ## Checker errors — one per class -/

/-- error: unknown name 'lof' (did you mean 'lo'?) -/
#guard_msgs in
#spytial.spec sExample with [orientation lof below]

/-- error: type 'STree' cannot occur in values of 'SBDD'; vocabulary of 'SBDD': SBDD, String, hi, lo, scrutinee, v -/
#guard_msgs in
#spytial.spec sExample with [hideAtom STree]

/-- error: unknown constructor label 'ttt'; known labels of 'SBDD': ff, tt -/
#guard_msgs in
#spytial.spec sExample with [atomColor {x : SBDD | @:x = ttt} "red"]

/-- error: constructor 'SRB.nil' belongs to 'SRB', which cannot occur in values of 'SBDD' -/
#guard_msgs in
#spytial.spec sExample with [atomColor {x : SBDD | @:x = SRB.nil} "red"]

/-- error: this position selects atoms (arity 1), but the selector has arity 2 -/
#guard_msgs in
#spytial.spec sExample with [hideAtom lo]

/-- error: this position selects pairs (arity 2), but the selector has arity 1 -/
#guard_msgs in
#spytial.spec sExample with [orientation SBDD below]

/-- error: join of arity 1 and arity 1 has no columns left -/
#guard_msgs in
#spytial.spec sExample with [hideAtom SBDD . SBDD]

/-- error: the operand of ^ must have arity 2, got 1 -/
#guard_msgs in
#spytial.spec sExample with [orientation ^SBDD below]

/-- error: operands of + must have equal arity, got 2 and 1 -/
#guard_msgs in
#spytial.spec sExample with [hideAtom lo + SBDD]

/-- error: a comprehension binder domain must have arity 1, got 2 -/
#guard_msgs in
#spytial.spec sExample with [hideAtom {x : lo | @:x = tt}]

/-- error: unknown relation 'lof' (did you mean 'lo'?) -/
#guard_msgs in
#spytial.spec sExample with [edgeColor lof "red"]

/-- error: unknown direction 'sideways' (expected above, below, left, right, directlyAbove, directlyBelow, directlyLeft, directlyRight) -/
#guard_msgs in
#spytial.spec sExample with [orientation lo sideways]

/--
error: unknown Spytial op 'orientate'; known ops: align, atomColor, attribute, cyclic, edgeColor, flag, group, hideAtom, hideField, icon, inferredEdge, orientation, size, tag
-/
#guard_msgs in
#spytial.spec sExample with [orientate lo below]

/-- error: missing argument 2; usage: atomColor <selector> <css-color> -/
#guard_msgs in
#spytial.spec sExample with [atomColor SBDD]

/-- error: unexpected extra argument; usage: hideAtom <selector> -/
#guard_msgs in
#spytial.spec sExample with [hideAtom SBDD String]

/-- error: expected a rotation direction (clockwise, counterclockwise); usage: cyclic <selector> [clockwise|counterclockwise] -/
#guard_msgs in
#spytial.spec sExample with [cyclic {x, y : SBDD | x->y in lo} "clockwise"]

/-! ## Spec-introduced names are in scope for later ops -/

/--
info: constraints:
  - group: {selector: "SBDD", name: "cluster"}
directives:
  - inferredEdge: {name: "hop", selector: "lo.hi", color: "#000000", style: solid}
  - edgeColor: {field: "hop", value: "purple", style: solid}
-/
#guard_msgs in
#spytial.spec sExample with [
  group SBDD cluster,
  inferredEdge hop lo.hi,
  edgeColor hop "purple"
]

/-! ## Multiplicity formulas -/

/--
info: constraints:
  - hideAtom: {selector: "{x : SBDD | some x.lo and no x.hi}"}
  - hideAtom: {selector: "{x : SBDD | lone x.lo or one x.hi}"}
  - hideAtom: {selector: "{x : SBDD | some lo}"}
-/
#guard_msgs in
#spytial.spec sExample with [
  hideAtom {x : SBDD | some x.lo && no x.hi},
  hideAtom {x : SBDD | lone x.lo || one x.hi},
  hideAtom {x : SBDD | some lo}
]

/-- error: unknown name 'bogus'; vocabulary of 'SBDD': SBDD, String, hi, lo, scrutinee, v -/
#guard_msgs in
#spytial.spec sExample with [hideAtom {x : SBDD | some bogus}]

/-! ## `@num:` label projection -/

/--
info: directives:
  - atomColor: {selector: "{x : SRB | @num:(x.key) = 1}", value: "red"}
-/
#guard_msgs in
#spytial.spec sRB with [
  atomColor {x : SRB | @num:(x.key) = 1} "red"
]

/-! ## Sort-typed field: dropped from vocabulary, scope stays strict -/

/-- A `Type`-valued field is proof-like — the walker drops it, so it is neither
    vocabulary nor a reason to open the scope. -/
public structure SCarrier where
  carrier : Type
  tag : Nat

public def sCarrier : SCarrier := { carrier := Nat, tag := 0 }

/-- error: unknown name 'carrier' (did you mean 'SCarrier'?) -/
#guard_msgs in
#spytial.spec sCarrier with [hideAtom carrier]

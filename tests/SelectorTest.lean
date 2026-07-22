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

/-! ## Precedence battery — the Forge re-tier

`implies` binds tighter than `or`/`iff` and is the only right-associative
connective; multiplicity applies to a whole union; difference is left-associative. -/

/--
info: constraints:
  - hideAtom: {selector: "{x : SBDD | some x.lo or some x.hi implies no x.lo}"}
  - hideAtom: {selector: "{x : SBDD | some x.lo implies some x.hi implies no x.lo}"}
  - hideAtom: {selector: "{x : SBDD | some x.lo implies some x.hi else no x.lo}"}
  - hideAtom: {selector: "{x : SBDD | some SBDD + String}"}
  - hideAtom: {selector: "{x : SBDD | #x.lo = 1}"}
  - orientation: {selector: "~lo", directions: [below]}
-/
#guard_msgs in
#spytial.spec sExample with [
  hideAtom {x : SBDD | some x.lo || some x.hi => no x.lo},
  hideAtom {x : SBDD | some x.lo => some x.hi => no x.lo},
  hideAtom {x : SBDD | some x.lo => some x.hi else no x.lo},
  hideAtom {x : SBDD | some SBDD + String},
  hideAtom {x : SBDD | #x.lo = 1},
  orientation ~lo below
]

/-- info: constraints:
  - hideAtom: {selector: "SColor - Nat - SRB"}
-/
#guard_msgs in
#spytial.spec sRB with [hideAtom SColor - Nat - SRB]

/-! ## Word connectives (both spellings lower the same), xor / iff / ite / not -/

/--
info: constraints:
  - hideAtom: {selector: "{x : SBDD | some x.lo and no x.hi or one x.lo}"}
  - hideAtom: {selector: "{x : SBDD | some x.lo xor no x.hi}"}
  - hideAtom: {selector: "{x : SBDD | some x.lo iff no x.hi}"}
  - hideAtom: {selector: "{x : SBDD | some x.lo implies no x.hi else one x.lo}"}
  - hideAtom: {selector: "{x : SBDD | not some x.lo}"}
-/
#guard_msgs in
#spytial.spec sExample with [
  hideAtom {x : SBDD | some x.lo and no x.hi or one x.lo},
  hideAtom {x : SBDD | some x.lo xor no x.hi},
  hideAtom {x : SBDD | some x.lo iff no x.hi},
  hideAtom {x : SBDD | some x.lo implies no x.hi else one x.lo},
  hideAtom {x : SBDD | not some x.lo}
]

/-! ## Quantifiers (leading `disj`, comma name-groups, typed groups) and `let` -/

/--
info: constraints:
  - hideAtom: {selector: "{x : SBDD | all y : SBDD | some y.lo}"}
  - hideAtom: {selector: "{x : SBDD | some disj y, z : SBDD | y != z}"}
  - hideAtom: {selector: "{x : SBDD | no y : SBDD, w : String | @:y = tt}"}
-/
#guard_msgs in
#spytial.spec sExample with [
  hideAtom {x : SBDD | all y : SBDD | some y.lo},
  hideAtom {x : SBDD | some disj y, z : SBDD | y != z},
  hideAtom {x : SBDD | no y : SBDD, w : String | @:y = tt}
]

-- `let` desugars by substitution; a later binder shadows it (`a` below is the
-- `all`-bound `a`, not `lo`).
/--
info: constraints:
  - hideAtom: {selector: "{x : SBDD | some x.lo and no x.hi}"}
  - hideAtom: {selector: "{x : SBDD | all a : SBDD | some a}"}
-/
#guard_msgs in
#spytial.spec sExample with [
  hideAtom {x : SBDD | let a = x.lo, b = x.hi | some a and no b},
  hideAtom {x : SBDD | let a = lo | all a : SBDD | some a}
]

/-! ## Integer layer — `#`, `@num:`, builtins, aggregators, box join, counting -/

/--
info: directives:
  - atomColor: {selector: "{x : SRB | @num:(x.key) < 5}", value: "red"}
  - atomColor: {selector: "{x : SRB | add[@num:(x.key), 1] > 2}", value: "red"}
  - atomColor: {selector: "{x : SRB | abs[@num:(x.key)] >= 1}", value: "red"}
  - atomColor: {selector: "{x : SRB | min[SRB.key] <= 3}", value: "red"}
-/
#guard_msgs in
#spytial.spec sRB with [
  atomColor {x : SRB | @num:(x.key) < 5} "red",
  atomColor {x : SRB | add[@num:(x.key), 1] > 2} "red",
  atomColor {x : SRB | abs[@num:(x.key)] >= 1} "red",
  atomColor {x : SRB | min[SRB.key] <= 3} "red"
]

-- Counting idiom and relational box join (`a[b] ≡ b.a`).
/--
info: constraints:
  - hideAtom: {selector: "{x : SBDD | #{y : SBDD | some y.lo} = 2}"}
  - hideAtom: {selector: "SBDD.lo"}
-/
#guard_msgs in
#spytial.spec sExample with [
  hideAtom {x : SBDD | #{y : SBDD | some y.lo} = 2},
  hideAtom lo[SBDD]
]

/-! ## Negated comparisons (`!in`, `not in` — both lower to `!in`) -/

/--
info: constraints:
  - hideAtom: {selector: "{x : SBDD | x.lo !in x.hi}"}
  - hideAtom: {selector: "{x : SBDD | x.lo !in x.hi}"}
-/
#guard_msgs in
#spytial.spec sExample with [
  hideAtom {x : SBDD | x.lo !in x.hi},
  hideAtom {x : SBDD | x.lo not in x.hi}
]

/-! ## Engine-bug forms — accepted, lowered verbatim, warned (upstream SGQ issues) -/

/--
warning: the SGQ engine evaluates `none` to the string "none", not the empty set — use `no e` for emptiness tests (upstream bug)
---
info: constraints:
  - hideAtom: {selector: "{x : SBDD | no none}"}
-/
#guard_msgs in
#spytial.spec sExample with [hideAtom {x : SBDD | no none}]

/--
warning: the SGQ engine evaluates `a ni b` as ¬(a in b); Forge defines `a ni b ≡ b in a` — the two differ, so this constraint may evaluate opposite to its intent (upstream bug)
---
info: constraints:
  - hideAtom: {selector: "{x : SBDD | x.lo ni x.hi}"}
-/
#guard_msgs in
#spytial.spec sExample with [hideAtom {x : SBDD | x.lo ni x.hi}]

/--
warning: the SGQ engine currently throws on `<:` (domain restriction) at render — in a constraint position this kills the render (upstream bug)
---
info: constraints:
  - orientation: {selector: "SBDD <: lo", directions: [below]}
-/
#guard_msgs in
#spytial.spec sExample with [orientation SBDD <: lo below]

/--
warning: the SGQ engine currently throws on `:>` (range restriction) at render — in a constraint position this kills the render (upstream bug)
---
info: constraints:
  - orientation: {selector: "lo :> SBDD", directions: [below]}
-/
#guard_msgs in
#spytial.spec sExample with [orientation lo :> SBDD below]

/--
warning: the SGQ engine currently throws on `++` (override) at render — in a constraint position this kills the render (upstream bug)
---
info: constraints:
  - orientation: {selector: "lo ++ hi", directions: [below]}
-/
#guard_msgs in
#spytial.spec sExample with [orientation lo ++ hi below]

/--
warning: the SGQ engine silently drops arrow-multiplicity annotations — `A one -> lone B` evaluates as the plain product `A -> B` (upstream bug)
---
info: constraints:
  - orientation: {selector: "SBDD one -> lone SBDD", directions: [below]}
-/
#guard_msgs in
#spytial.spec sExample with [orientation SBDD one -> lone SBDD below]

/--
warning: the SGQ engine does not evaluate backquote atom literals — it renders an `UNIMPLEMENTED` placeholder (upstream bug)
---
info: constraints:
  - hideAtom: {selector: "{x : SBDD | x = `a0}"}
-/
#guard_msgs in
#spytial.spec sExample with [hideAtom {x : SBDD | x = `a0}]

/--
warning: the SGQ engine evaluates `sum[e]` to the empty set rather than summing its atoms (upstream bug)
---
info: directives:
  - atomColor: {selector: "{x : SRB | sum[SRB.key] > 2}", value: "red"}
-/
#guard_msgs in
#spytial.spec sRB with [atomColor {x : SRB | sum[SRB.key] > 2} "red"]

/-! ## Integer-layer type errors — one per class -/

/-- error: this position expects a relational expression, but the selector is an integer (`#`, a numeral, `@num:`, or an int builtin) -/
#guard_msgs in
#spytial.spec sExample with [hideAtom {x : SBDD | some #x.lo}]

/-- error: this position expects a relational expression, but the selector is an integer (`#`, a numeral, `@num:`, or an int builtin) -/
#guard_msgs in
#spytial.spec sExample with [hideAtom #lo + hi]

/-- error: this position expects an integer expression (`#e`, a numeral, `@num:e`, or an int builtin) -/
#guard_msgs in
#spytial.spec sExample with [hideAtom {x : SBDD | #x.lo = lo}]

/-! ## Step-0 pin — a relation literally named `some` stays usable

`SWeird.mk` has fields `some` and `one`; `.both` on the formula category keeps
the multiplicity keyword and the bare relation distinguishable by longest-match. -/

public inductive SWeird where
  | mk (some one : SWeird)
  | leaf

public def sWeird : SWeird := .leaf

/-- info: constraints:
  - hideAtom: {selector: "{x : SWeird | some some and one one}"}
-/
#guard_msgs in
#spytial.spec sWeird with [hideAtom {x : SWeird | some some and one one}]

/-! ## Products chain left; quantifiers keep their parens under a connective -/

/--
warning: arity-3 selector in a pair position: only the first and last columns of each tuple are used
---
info: constraints:
  - orientation: {selector: "SBDD->SBDD->SBDD", directions: [below]}
-/
#guard_msgs in
#spytial.spec sExample with [orientation SBDD -> SBDD -> SBDD below]

/--
info: constraints:
  - hideAtom: {selector: "{x : SBDD | (all y : SBDD | some y.lo) and some x.hi}"}
-/
#guard_msgs in
#spytial.spec sExample with [
  hideAtom {x : SBDD | (all y : SBDD | some y.lo) && some x.hi}
]

/-- error: cannot use let-bound 'e' here: it refers to 'x', which a nearer binder shadows — the substitution would be captured; rename the inner binder -/
#guard_msgs in
#spytial.spec sExample with [hideAtom {x : SBDD | let e = x.lo | all x : SBDD | some e}]

/-! ## Token-table hygiene — the DSL must not reserve words or steal prefixes

These fail to *compile* if a selector rule leaks into the global token table
(`ni` as a keyword; a `"!in"` atom stealing the prefix of `!i…` negations). -/

def hygieneNi : Nat := 5
def hygieneNotIn (input : Bool) : Bool := !input
def hygieneNotInBounds (inBounds : Bool) : Bool := !inBounds
example : Nat := let and := 5; and
example : Nat := let ni := hygieneNi; ni
example : Option Nat := some 3

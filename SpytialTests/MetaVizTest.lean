import SpytialLean
import SpytialTests.WalkCanon

/-! # Tests for `SpytialLean.MetaViz` and the `Expr` view

The meta-type policy, pinned through `#spytial.datum` exactly as a user hits
it: a `Name` is one leaf labeled with its literal, and an `Expr` renders as
its registered syntax view — flattened spines, binder back-edges, implicit
stubs — with no no-identity warning. A `#guard_msgs` here also pins the
*absence* of warnings. -/

open Lean

/--
info: {"relations": [],
 "atoms": [{"type": "Name", "label": "`HAdd.hAdd", "id": "atom_0"}]}
-/
#guard_msgs in
#spytial.datum (`HAdd.hAdd : Name)

/--
info: {"relations": [],
 "atoms": [{"type": "Name", "label": "anonymous", "id": "atom_0"}]}
-/
#guard_msgs in
#spytial.datum (Name.anonymous)

/--
info: {"relations":
 [{"types": ["Binder", "ExprViewNode"],
   "tuples": [],
   "name": "value",
   "id": "value"},
  {"types": ["Var", "Binder"],
   "tuples": [{"types": ["Var", "Binder"], "atoms": ["atom_3", "atom_1"]}],
   "name": "binder",
   "id": "binder"},
  {"types": ["Binder", "Var"],
   "tuples": [{"types": ["Binder", "Var"], "atoms": ["atom_1", "atom_3"]}],
   "name": "body",
   "id": "body"},
  {"types": ["Binder", "Sort"],
   "tuples": [{"types": ["Binder", "Sort"], "atoms": ["atom_1", "atom_2"]}],
   "name": "type",
   "id": "type"}],
 "atoms":
 [{"type": "Binder", "label": "fun x", "id": "atom_1"},
  {"type": "Sort", "label": "Prop", "id": "atom_2"},
  {"type": "Var", "label": "x", "id": "atom_3"}]}
-/
#guard_msgs in
#spytial.datum (Expr.lam `x (Expr.sort Level.zero) (Expr.bvar 0) BinderInfo.default)

/--
info: {"relations":
 [{"types": ["App", "Nat", "Const"],
   "tuples":
   [{"types": ["App", "Nat", "Const"], "atoms": ["atom_1", "atom_3", "atom_4"]},
    {"types": ["App", "Nat", "Const"],
     "atoms": ["atom_1", "atom_5", "atom_6"]}],
   "name": "args",
   "id": "args"},
  {"types": ["App", "ExprViewNode"],
   "tuples": [],
   "name": "implicit",
   "id": "implicit"},
  {"types": ["App", "Const"],
   "tuples": [{"types": ["App", "Const"], "atoms": ["atom_1", "atom_2"]}],
   "name": "fn",
   "id": "fn"}],
 "atoms":
 [{"type": "App", "label": "app", "id": "atom_1"},
  {"type": "Const", "label": "f", "id": "atom_2"},
  {"type": "Nat", "label": "0", "id": "atom_3"},
  {"type": "Const", "label": "a", "id": "atom_4"},
  {"type": "Nat", "label": "1", "id": "atom_5"},
  {"type": "Const", "label": "b", "id": "atom_6"}]}
-/
#guard_msgs in
#spytial.datum (Expr.app (Expr.app (Expr.const `f []) (Expr.const `a [])) (Expr.const `b []))

/-! ## The Expr view: implicit collapse, loose bvars, the goal tactic -/

/--
info: {"relations":
 [{"types": ["App", "Nat", "Lit"],
   "tuples":
   [{"types": ["App", "Nat", "Lit"], "atoms": ["atom_1", "atom_3", "atom_4"]}],
   "name": "args",
   "id": "args"},
  {"types": ["App", "Implicit"],
   "tuples": [{"types": ["App", "Implicit"], "atoms": ["atom_1", "atom_5"]}],
   "name": "implicit",
   "id": "implicit"},
  {"types": ["App", "Const"],
   "tuples": [{"types": ["App", "Const"], "atoms": ["atom_1", "atom_2"]}],
   "name": "fn",
   "id": "fn"}],
 "atoms":
 [{"type": "App", "label": "app", "id": "atom_1"},
  {"type": "Const", "label": "id", "id": "atom_2"},
  {"type": "Nat", "label": "0", "id": "atom_3"},
  {"type": "Lit", "label": "5", "id": "atom_4"},
  {"type": "Implicit", "label": "Nat", "id": "atom_5"}]}
-/
#guard_msgs in
#spytial.datum (Expr.app (Expr.app (Expr.const `id [Level.zero.succ]) (Expr.const `Nat [])) (Expr.lit (.natVal 5)))

/--
info: {"relations": [],
 "atoms": [{"type": "Loose", "label": "#7 loose", "id": "atom_1"}]}
-/
#guard_msgs in
#spytial.datum (Expr.bvar 7)

-- `full`: every argument at its true position, no stubs — the implicit `Nat`
-- of `@id Nat 5` is `args[0]`'s `Const`. Reached only through the props
-- entry; the ops whose types/relations the datum lacks are gated out.
/--
info: {"dataInstance":
 {"relations":
  [{"types": ["App", "Nat", "univ"],
    "tuples":
    [{"types": ["App", "Nat", "Const"],
      "atoms": ["atom_0", "atom_2", "atom_3"]},
     {"types": ["App", "Nat", "Lit"], "atoms": ["atom_0", "atom_4", "atom_5"]}],
    "name": "args",
    "id": "args"},
   {"types": ["App", "ExprViewNode"],
    "tuples": [],
    "name": "implicit",
    "id": "implicit"},
   {"types": ["App", "Const"],
    "tuples": [{"types": ["App", "Const"], "atoms": ["atom_0", "atom_1"]}],
    "name": "fn",
    "id": "fn"}],
  "atoms":
  [{"type": "App", "label": "app", "id": "atom_0"},
   {"type": "Const", "label": "id", "id": "atom_1"},
   {"type": "Nat", "label": "0", "id": "atom_2"},
   {"type": "Const", "label": "Nat", "id": "atom_3"},
   {"type": "Nat", "label": "1", "id": "atom_4"},
   {"type": "Lit", "label": "5", "id": "atom_5"}]},
 "cndSpec":
 "{\"constraints\":\n [{\"hideAtom\":\n   {\"source\":\n    {\"text\":\n     \"hideAtom {x : univ |\\n    let source = (args) . univ . univ,\\n        label  = univ . (args) . univ,\\n        target = univ . (univ . (args))\\n    | x in label && x !in source && x !in target}\",\n     \"location\": \"ExprView.lean:N\"},\n    \"selector\":\n    \"{x : univ | x in univ.args.univ and x !in args.univ.univ and x !in univ.(univ.args)}\"}}]}"}
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let e := Lean.mkApp2 (.const ``id [.succ .zero]) (.const ``Nat []) (Lean.mkRawNatLit 5)
  Lean.logInfo (maskLines (← SpytialLean.exprViewProps e { full := true }).pretty)

example (n : Nat) : n + 0 = n := by
  spytial.goal
  simp

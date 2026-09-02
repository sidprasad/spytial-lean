import SpytialLean

/-! # Tests for `SpytialLean.MetaViz` and the `Expr` view

The meta-type policy, pinned through `#spytial.datum` as a user hits it: a
`Name` is one leaf labeled with its literal, and an `Expr` draws as its
syntax view. `ExprShape` is the view's declared vocabulary; a spec over
`Expr` checks against it, and the emitted datum stays inside it. -/

open Lean SpytialLean

/--
info: {"relations": [],
 "atoms": [{"type": "Name", "label": "`HAdd.hAdd", "id": "atom_1"}]}
-/
#guard_msgs in
#spytial.datum (`HAdd.hAdd : Name)

/--
info: {"relations": [],
 "atoms": [{"type": "Name", "label": "anonymous", "id": "atom_1"}]}
-/
#guard_msgs in
#spytial.datum (Name.anonymous)

/-! ## Binder back-edge, implicit collapse, loose index -/

/--
info: {"relations":
 [{"types": ["Var", "Binder"],
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
 [{"types": ["App", "Nat", "Lit"],
   "tuples":
   [{"types": ["App", "Nat", "Lit"], "atoms": ["atom_1", "atom_4", "atom_5"]}],
   "name": "args",
   "id": "args"},
  {"types": ["App", "Implicit"],
   "tuples": [{"types": ["App", "Implicit"], "atoms": ["atom_1", "atom_3"]}],
   "name": "implicit",
   "id": "implicit"},
  {"types": ["App", "Const"],
   "tuples": [{"types": ["App", "Const"], "atoms": ["atom_1", "atom_2"]}],
   "name": "fn",
   "id": "fn"}],
 "atoms":
 [{"type": "App", "label": "app", "id": "atom_1"},
  {"type": "Const", "label": "id", "id": "atom_2"},
  {"type": "Implicit", "label": "Nat", "id": "atom_3"},
  {"type": "Nat", "label": "0", "id": "atom_4"},
  {"type": "Lit", "label": "5", "id": "atom_5"}]}
-/
#guard_msgs in
#spytial.datum (Expr.app (Expr.app (Expr.const `id [Level.zero.succ]) (Expr.const `Nat [])) (Expr.lit (.natVal 5)))

-- `spytial.expr.full`: every argument at its position, no stubs
/--
info: {"relations":
 [{"types": ["App", "Nat", "univ"],
   "tuples":
   [{"types": ["App", "Nat", "Const"], "atoms": ["atom_1", "atom_3", "atom_4"]},
    {"types": ["App", "Nat", "Lit"], "atoms": ["atom_1", "atom_5", "atom_6"]}],
   "name": "args",
   "id": "args"},
  {"types": ["App", "Const"],
   "tuples": [{"types": ["App", "Const"], "atoms": ["atom_1", "atom_2"]}],
   "name": "fn",
   "id": "fn"}],
 "atoms":
 [{"type": "App", "label": "app", "id": "atom_1"},
  {"type": "Const", "label": "id", "id": "atom_2"},
  {"type": "Nat", "label": "0", "id": "atom_3"},
  {"type": "Const", "label": "Nat", "id": "atom_4"},
  {"type": "Nat", "label": "1", "id": "atom_5"},
  {"type": "Lit", "label": "5", "id": "atom_6"}]}
-/
#guard_msgs in
set_option spytial.expr.full true in
#spytial.datum (Expr.app (Expr.app (Expr.const `id [Level.zero.succ]) (Expr.const `Nat [])) (Expr.lit (.natVal 5)))

/--
info: {"relations": [],
 "atoms": [{"type": "Loose", "label": "#7 loose", "id": "atom_1"}]}
-/
#guard_msgs in
#spytial.datum (Expr.bvar 7)

/-! ## The declared shape is the vocabulary

A spec over `Expr` resolves the shape's constructors as atom types and its
fields as relations; a name outside the shape is an error, not a warning. -/

/--
info: {"directives":
 [{"atomStyle": {"selector": "Binder", "fillStyle": {"color": "#ffffff"}}},
  {"edgeStyle":
   {"lineStyle": {"pattern": "dashed", "color": "#000000"}, "field": "args"}}]}
-/
#guard_msgs in
#spytial.spec (Expr.bvar 0) with [atomStyle Binder (fillStyle "#ffffff"),
                                  edgeStyle args (lineStyle "#000000" dashed)]

/-- error: unknown name 'Bindr' (did you mean 'Binder', 'binder'?) -/
#guard_msgs in
#spytial.spec (Expr.bvar 0) with [atomStyle Bindr (fillStyle "#ffffff")]

/-! ## The emission stays inside the declaration -/

open Lean.Elab.Command in
/-- `#conforms <e : Expr>`: every atom type and relation the view emits for
    `e` is one the scope of `Lean.Expr` (which follows `ExprShape`) knows. -/
elab "#conforms " t:term : command => do
  liftTermElabM do
    let e ← Lean.Elab.Term.elabTerm t (some (mkConst ``Expr))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let scope ← SelScope.ofType ``Lean.Expr
    let di ← relationalize (← instantiateMVars e)
    let types := scope.types.fold (init := (∅ : Std.HashSet String)) fun s _ v => s.insert v
    for a in di.atoms do
      unless types.contains a.type || a.type == "Nat" do
        throwError "atom type '{a.type}' is not in the declared shape"
    for r in di.relations do
      unless scope.rels.contains r.name do
        throwError "relation '{r.name}' is not in the declared shape"
    if scope.lenient then throwError "the scope went lenient"

#conforms Expr.lam `x (.sort .zero) (.bvar 0) .default
#conforms mkApp2 (.const ``id [.succ .zero]) (.const ``Nat []) (mkRawNatLit 5)
#conforms Expr.letE `y (.const ``Nat []) (mkRawNatLit 1) (.bvar 0) false
#conforms Expr.mdata {} (Expr.proj ``Prod 0 (.bvar 9))

example (n : Nat) : n + 0 = n := by
  spytial.goal
  simp

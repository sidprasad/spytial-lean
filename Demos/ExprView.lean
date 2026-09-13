import SpytialLean

open Lean Meta Elab Command SpytialLean

/-! # A `Lean.Expr` as the tactic author sees it -/

/-- `#exprviz <term>` draws the elaborated term's syntax tree. -/
syntax (name := exprvizCmd) "#exprviz " term : command

@[command_elab exprvizCmd]
def elabExprviz : CommandElab := fun
  | stx@`(#exprviz $t:term) => do
    let props ← liftTermElabM do
      let e ← Term.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      exprViewProps (← instantiateMVars e)
    liftCoreM <| Widget.savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx => throwError "Unexpected syntax {stx}."

/-- `#exprviz.run <term : MetaM Expr>` draws the `Expr` a meta program returns. -/
syntax (name := exprvizRunCmd) "#exprviz.run " term : command

@[command_elab exprvizRunCmd]
unsafe def elabExprvizRun : CommandElab := fun
  | stx@`(#exprviz.run $t:term) => do
    let props ← liftTermElabM do
      let act ← Term.evalTerm (MetaM Expr) (mkApp (mkConst ``MetaM) (mkConst ``Expr)) t
      exprViewProps (← act)
    liftCoreM <| Widget.savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx => throwError "Unexpected syntax {stx}."

-- `x + 1` is not `Nat.add x 1`: a six-argument `HAdd.hAdd` spine, and `1`
-- is `OfNat.ofNat`, not a literal
#exprviz fun x : Nat => x + 1

set_option spytial.expr.full true in
#exprviz fun x : Nat => x + 1

#eval show MetaM Bool from do
  let e ← Term.TermElabM.run' (Term.elabTerm (← `((1 : Nat))) none)
  return e.isLit

-- `isApp` is false under `mdata`
#exprviz.run do
  let app := mkApp2 (.const ``Nat.add []) (mkRawNatLit 1) (mkRawNatLit 2)
  return .mdata (KVMap.empty.insert `noImplicitLambda (.ofBool true)) app

-- a metavariable assigned by `isDefEq` still reads `?m` until `instantiateMVars`
#exprviz.run do
  let m ← mkFreshExprMVar (some (mkConst ``Nat))
  let e := mkApp2 (.const ``Nat.add []) m (mkRawNatLit 1)
  discard <| isDefEq m (mkRawNatLit 7)
  return e

#exprviz.run do
  let m ← mkFreshExprMVar (some (mkConst ``Nat))
  let e := mkApp2 (.const ``Nat.add []) m (mkRawNatLit 1)
  discard <| isDefEq m (mkRawNatLit 7)
  instantiateMVars e

-- every variable links back to its binder; a loose index draws red
#spytial (Expr.lam `x (.const ``Nat []) (.lam `y (.const ``Nat []) (.bvar 1) .default) .default)

#spytial (Expr.lam `x (.const ``Nat []) (.bvar 3) .default)

-- the spec checks against the view's vocabulary
#spytial (Expr.lam `x (.const ``Nat []) (.bvar 0) .default) with [.., atomStyle Var (borderStyle "#2f6fba")]

-- the goal mid-proof, and a `refine` hole in place
example (n : Nat) : n + 0 = n := by
  spytial.goal
  simp

example : ∃ k : Nat, k + 1 = 2 := by
  refine ⟨?w, ?h⟩
  case h =>
    spytial.goal
    rfl

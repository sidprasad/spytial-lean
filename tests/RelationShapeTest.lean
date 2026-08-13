module

meta import SpytialLean.Relationalizer
meta import WalkCanon

open SpytialLean Lean Meta

public inductive MTree where
  | leaf (value : Nat)
  | node (left right : MTree)

/-! ## Stuck matches emit one ternary `scrutinee`

`scrutinee : (match, position, discriminant)` whatever the discriminant count:
the position is a walked `Nat` atom, not part of the relation's name. The
goldens are whole canonical instances, so an `scrutinee_i` family — or any
other change to the emission — fails them. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `t (mkConst ``MTree) fun t => do
    let tStx ← Lean.Elab.Term.exprToSyntax t
    let stx ← `(match $tStx:term with | .leaf v => v | .node _ _ => 0)
    let e ← Lean.Elab.Term.elabTermEnsuringType stx (some (mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    assertCanon "scrutinee.unary" (← relationalize (← instantiateMVars e))
      "Nat|match\nNat|0\nMTree|t\nscrutinee:0,1,2"

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `t (mkConst ``MTree) fun t => do
  withLocalDeclD `b (mkConst ``Bool) fun b => do
    let tStx ← Lean.Elab.Term.exprToSyntax t
    let bStx ← Lean.Elab.Term.exprToSyntax b
    let stx ← `(match $tStx:term, $bStx:term with
                  | .leaf v, true => v
                  | _, _ => 0)
    let e ← Lean.Elab.Term.elabTermEnsuringType stx (some (mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    assertCanon "scrutinee.binary" (← relationalize (← instantiateMVars e))
      "Nat|match\nNat|0\nMTree|t\nNat|1\nBool|b\nscrutinee:0,1,2;0,3,4"

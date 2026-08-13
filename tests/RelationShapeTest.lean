module

meta import SpytialLean.Relationalizer
meta import WalkCanon

open SpytialLean Lean Meta

public inductive MTree where
  | leaf (value : Nat)
  | node (left right : MTree)

public structure Cell where
  value : Nat
  tag : String
  deriving Inhabited

/-- Stuck at a structure type: the walker projects instead of decomposing. -/
opaque mystery : Cell

public def parity : Bool → Nat
  | true => 1
  | false => 0

/-! ## Stuck matches emit one ternary `scrutinee`

`(match, position, discriminant)`: the position is a walked atom, not part of
the relation's name. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `t (mkConst ``MTree) fun t => do
    let tStx ← Lean.Elab.Term.exprToSyntax t
    let stx ← `(match $tStx:term with | .leaf v => v | .node _ _ => 0)
    let e ← Lean.Elab.Term.elabTermEnsuringType stx (some (mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    assertCanon "scrutinee.unary" (← relationalize (← instantiateMVars e))
      "Nat|match\nNat|0\nMTree|t\nscrutinee[Nat,Nat,MTree]:0,1,2"

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
    let di ← relationalize (← instantiateMVars e)
    assertCanon "scrutinee.binary" di
      "Nat|match\nNat|0\nMTree|t\nNat|1\nBool|b\nscrutinee[Nat,Nat,MTree]:0,1,2;0,3,4"
    -- the relation's row freezes at the first tuple registered; every tuple
    -- still carries its own
    let some rel := di.relations.find? (·.name == "scrutinee")
      | throwError "scrutinee.binary: relation missing"
    let got := rel.tuples.map (·.types)
    unless got == #[#["Nat", "Nat", "MTree"], #["Nat", "Nat", "Bool"]] do
      throwError "scrutinee.binary.tuple-types: got {toString (repr got)}"

/-! ## Every column carries its own type

Constructor fields, enumerated function tables, and structure projections all
declare the child's type, not a second copy of the owner's. -/

#eval show MetaM Unit from do
  let cell := mkApp2 (mkConst ``Cell.mk) (mkRawNatLit 3) (mkStrLit "x")
  assertCanon "types.ctor" (← relationalize cell)
    "Cell|mk\nNat|3\nString|\"x\"\ntag[Cell,String]:0,2\nvalue[Cell,Nat]:0,1"

#eval show MetaM Unit from do
  assertCanon "types.table" (← relationalize (mkConst ``parity))
    "Bool → Nat|parity\nNat|0\nNat|1\nfalse[Bool → Nat,Nat]:0,1\ntrue[Bool → Nat,Nat]:0,2"

#eval show MetaM Unit from do
  assertCanon "types.projection" (← relationalize (mkConst ``mystery))
    "Cell|Cell\nNat|mystery.1\nString|mystery.2\ntag[Cell,String]:0,2\nvalue[Cell,Nat]:0,1"

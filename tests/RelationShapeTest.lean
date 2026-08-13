module

public import SpytialLean.Identity
meta import SpytialLean.Identity
public meta import SpytialLean.MetaEncode
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
    -- the relation row freezes at the first tuple; each carries its own
    let some rel := di.relations.find? (·.name == "scrutinee")
      | throwError "scrutinee.binary: relation missing"
    let got := rel.tuples.map (·.types)
    unless got == #[#["Nat", "Nat", "MTree"], #["Nat", "Nat", "Bool"]] do
      throwError "scrutinee.binary.tuple-types: got {toString (repr got)}"

/-! ## Every column carries its own type

The child's type, not a second copy of the owner's. -/

#eval show MetaM Unit from do
  let cell := mkApp2 (mkConst ``Cell.mk) (mkRawNatLit 3) (mkStrLit "x")
  assertCanon "types.ctor" (← relationalize cell)
    "Cell|mk\nNat|3\nString|\"x\"\ntag[Cell,String]:0,2\nvalue[Cell,Nat]:0,1"

#eval show MetaM Unit from do
  assertCanon "types.table" (← relationalize (mkConst ``parity))
    "Bool → Nat|parity\nBool|false\nBool|true\nNat|0\nNat|1\nmaps[Bool → Nat,Bool,Nat]:0,1,3;0,2,4"

#eval show MetaM Unit from do
  assertCanon "types.projection" (← relationalize (mkConst ``mystery))
    "Cell|Cell\nNat|mystery.1\nString|mystery.2\ntag[Cell,String]:0,2\nvalue[Cell,Nat]:0,1"

/-! ## Enumerable function fields are flat n-ary tables

One `(owner, d₁, …, dₖ, result)` relation per field, over the whole domain
product, lexicographic with the first binder outermost. -/

public structure BoolF where
  f : Bool → Nat

public def boolFVal : BoolF := { f := fun b => if b then 1 else 0 }

public inductive Q where | q0 | q1 | q2

public structure QStep where
  step : Q → Q

public def qStepVal : QStep :=
  { step := fun q => match q with | .q0 => .q1 | .q1 => .q2 | .q2 => .q0 }

public structure FinF where
  g : Fin 2 → Nat

public def finFVal : FinF := { g := fun i => i.val }

public structure DA where
  tr : Q → Bool → Q

public def daVal : DA :=
  { tr := fun q b => match q, b with
      | .q0, false => .q0
      | .q0, true  => .q1
      | .q1, false => .q2
      | .q1, true  => .q0
      | .q2, false => .q1
      | .q2, true  => .q2 }

public structure Proc where
  process : String → Nat

public def procVal : Proc := { process := fun s => s.length }

public structure PropRel where
  rel : Q → Q → Prop

public def propRelVal : PropRel := { rel := fun a b => a = b }

/-- One enumerable binder, one not: all-or-nothing, no partial trie. -/
public structure Mixed where
  m : Bool → String → Nat

public def mixedVal : Mixed := { m := fun b s => if b then s.length else 0 }

#eval show MetaM Unit from do
  assertCanon "table.bool" (← relationalize (mkConst ``boolFVal))
    "BoolF|mk\nBool|false\nBool|true\nNat|0\nNat|1\nf[BoolF,Bool,Nat]:0,1,3;0,2,4"

#eval show MetaM Unit from do
  assertCanon "table.enum" (← relationalize (mkConst ``qStepVal))
    "QStep|mk\nQ|q0\nQ|q1\nQ|q2\nQ|q1\nQ|q2\nQ|q0\nstep[QStep,Q,Q]:0,1,4;0,2,5;0,3,6"

#eval show MetaM Unit from do
  assertCanon "table.fin" (← relationalize (mkConst ``finFVal))
    "FinF|mk\nFin|mk\nNat|0\nFin|mk\nNat|1\nNat|0\nNat|1\ng[FinF,Fin,Nat]:0,1,5;0,3,6\nval[Fin,Nat]:1,2;3,4"

#eval show MetaM Unit from do
  assertCanon "table.product" (← relationalize (mkConst ``daVal))
    "DA|mk\nQ|q0\nQ|q1\nQ|q2\nBool|false\nBool|true\nQ|q0\nQ|q1\nQ|q2\nQ|q0\nQ|q1\nQ|q2\ntr[DA,Q,Bool,Q]:0,1,4,6;0,1,5,7;0,2,4,8;0,2,5,9;0,3,4,10;0,3,5,11"

/-! ## What stays a labeled λ leaf

A non-enumerable domain — in any binder position — a domain product over
`maxTableTuples`, and (until decidable enumeration lands) a `Prop` codomain
all keep the λ atom and the binary owner→field edge. -/

#eval show MetaM Unit from do
  assertCanon "table.nonenum" (← relationalize (mkConst ``procVal))
    "Proc|mk\nString → Nat|λ s\nprocess[Proc,String → Nat]:0,1"

#eval show MetaM Unit from do
  assertCanon "table.partial" (← relationalize (mkConst ``mixedVal))
    "Mixed|mk\nBool → String → Nat|λ b\nm[Mixed,Bool → String → Nat]:0,1"

#eval show MetaM Unit from do
  assertCanon "table.cap" (← relationalize (mkConst ``daVal) { maxTableTuples := 3 })
    "DA|mk\nQ → Bool → Q|λ q\ntr[DA,Q → Bool → Q]:0,1"

#eval show MetaM Unit from do
  assertCanon "table.prop" (← relationalize (mkConst ``propRelVal))
    "PropRel|mk\nQ → Q → Prop|λ a\nrel[PropRel,Q → Q → Prop]:0,1"

/-! ## Root-level functions tabulate under `maps`

No field owns them, so the λ atom is column 0. -/

private meta def boolLam : MetaM Expr :=
  withLocalDeclD `b (mkConst ``Bool) fun b => do
    mkLambdaFVars #[b] (← mkAppM ``cond #[b, mkRawNatLit 1, mkRawNatLit 0])

#eval show MetaM Unit from do
  assertCanon "table.root" (← relationalize (← boolLam))
    "Bool → Nat|λ b\nBool|false\nBool|true\nNat|0\nNat|1\nmaps[Bool → Nat,Bool,Nat]:0,1,3;0,2,4"

/-! ## Identity decides whether a domain value and a result are one atom -/

public inductive QI where | q0 | q1 | q2
  deriving SpytialIdentity

public structure DAI where
  tr : QI → Bool → QI

public def daiVal : DAI :=
  { tr := fun q b => match q, b with
      | .q0, false => .q0
      | .q0, true  => .q1
      | .q1, false => .q2
      | .q1, true  => .q0
      | .q2, false => .q1
      | .q2, true  => .q2 }

#eval show MetaM Unit from do
  assertCanon "table.identity" (← relationalize (mkConst ``daiVal))
    "DAI|mk\nQI|q0\nQI|q1\nQI|q2\nBool|false\nBool|true\ntr[DAI,QI,Bool,QI]:0,1,4,1;0,1,5,2;0,2,4,3;0,2,5,1;0,3,4,2;0,3,5,3"

/-! ## The two-pass reference walks the same tables -/

#eval show MetaM Unit from do
  assertMatchesReference "diff.table.bool" (mkConst ``boolFVal)
  assertMatchesReference "diff.table.enum" (mkConst ``qStepVal)
  assertMatchesReference "diff.table.fin" (mkConst ``finFVal)
  assertMatchesReference "diff.table.product" (mkConst ``daVal)
  assertMatchesReference "diff.table.cap" (mkConst ``daVal) { maxTableTuples := 3 }
  assertMatchesReference "diff.table.maps" (mkConst ``parity)
  assertMatchesReference "diff.table.identity" (mkConst ``daiVal)
  assertMatchesReference "diff.table.root" (← boolLam)

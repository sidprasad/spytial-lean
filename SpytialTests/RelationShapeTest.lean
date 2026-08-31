module

public import SpytialLean.Identity
meta import SpytialLean.Identity
public meta import SpytialLean.MetaEncode
meta import SpytialLean.Relationalizer
meta import SpytialTests.WalkCanon

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

/-! ## Stuck matches emit one ternary `scrutinee`, `(match, position,
discriminant)`: the position is a walked atom, not part of the relation name. -/

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

/-! ## Every column carries its own type, not a copy of the owner's -/

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

/-! ## Enumerable function fields are flat n-ary tables: one
`(owner, d₁, …, dₖ, result)` relation per field over the whole domain product,
lexicographic with the first binder outermost. -/

public structure BoolF where
  f : Bool → Nat

public def boolFVal : BoolF := { f := fun b => if b then 1 else 0 }

public inductive Q where | q0 | q1 | q2
  deriving DecidableEq

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

/-- One enumerable binder, one not: all-or-nothing, no partial trie. -/
public structure Mixed where
  m : Bool → String → Nat

public def mixedVal : Mixed := { m := fun b s => if b then s.length else 0 }

#eval show MetaM Unit from do
  assertCanon "table.bool" (← relationalize (mkConst ``boolFVal))
    "BoolF|mk\nBool|false\nBool|true\nNat|0\nNat|1\nf[BoolF,Bool,Nat]:0,1,3;0,2,4"

#eval show MetaM Unit from do
  assertCanon "table.enum" (← relationalize (mkConst ``qStepVal))
    "QStep|mk\nQ|q0\nQ|q1\nQ|q2\nstep[QStep,Q,Q]:0,1,2;0,2,3;0,3,1"

#eval show MetaM Unit from do
  assertCanon "table.fin" (← relationalize (mkConst ``finFVal))
    "FinF|mk\nFin|mk\nNat|0\nFin|mk\nNat|1\ng[FinF,Fin,Nat]:0,1,2;0,3,4\nval[Fin,Nat]:1,2;3,4"

#eval show MetaM Unit from do
  assertCanon "table.product" (← relationalize (mkConst ``daVal))
    "DA|mk\nQ|q0\nQ|q1\nQ|q2\nBool|false\nBool|true\ntr[DA,Q,Bool,Q]:0,1,4,1;0,1,5,2;0,2,4,3;0,2,5,1;0,3,4,2;0,3,5,3"

/-! ## What stays a labeled λ leaf: a non-enumerable domain in any binder
position, and a domain product over `maxTableTuples`. -/

#eval show MetaM Unit from do
  assertCanon "table.nonenum" (← relationalize (mkConst ``procVal))
    "Proc|mk\nString → Nat|λ s\nprocess[Proc,String → Nat]:0,1"

#eval show MetaM Unit from do
  assertCanon "table.partial" (← relationalize (mkConst ``mixedVal))
    "Mixed|mk\nBool → String → Nat|λ b\nm[Mixed,Bool → String → Nat]:0,1"

#eval show MetaM Unit from do
  assertCanon "table.cap" (← relationalize (mkConst ``daVal) { maxTableTuples := 3 })
    "DA|mk\nQ → Bool → Q|λ q\ntr[DA,Q → Bool → Q]:0,1"

/-! ## Root-level functions tabulate under `maps`, the λ atom in column 0 -/

private meta def boolLam : MetaM Expr :=
  withLocalDeclD `b (mkConst ``Bool) fun b => do
    mkLambdaFVars #[b] (← mkAppM ``cond #[b, mkRawNatLit 1, mkRawNatLit 0])

#eval show MetaM Unit from do
  assertCanon "table.root" (← relationalize (← boolLam))
    "Bool → Nat|λ b\nBool|false\nBool|true\nNat|0\nNat|1\nmaps[Bool → Nat,Bool,Nat]:0,1,3;0,2,4"

/-! ## Decidable `Prop` codomains are relation tuples: no result column, a tuple
exactly where the proposition decides true. One undecided point bails it all. -/

public structure PropRel where
  rel : Q → Q → Prop

public def propRelVal : PropRel :=
  { rel := fun a b => a = b ∨ (a = Q.q0 ∧ b = Q.q2) }

/-- One true point out of nine: elements no tuple names never become atoms. -/
public structure Sparse where
  rel : Q → Q → Prop

public def sparseVal : Sparse := { rel := fun a b => a = Q.q0 ∧ b = Q.q1 }

public structure Never where
  rel : Q → Q → Prop

public def neverVal : Never := { rel := fun _ _ => False }

opaque myProp : Q → Prop

public structure Undec where
  p : Q → Prop

public def undecVal : Undec := { p := fun q => myProp q }

#eval show MetaM Unit from do
  assertCanon "prop.table" (← relationalize (mkConst ``propRelVal))
    "PropRel|mk\nQ|q0\nQ|q2\nQ|q1\nrel[PropRel,Q,Q]:0,1,1;0,1,2;0,3,3;0,2,2"

#eval show MetaM Unit from do
  assertCanon "prop.sparse" (← relationalize (mkConst ``sparseVal))
    "Sparse|mk\nQ|q0\nQ|q1\nrel[Sparse,Q,Q]:0,1,2"

#eval show MetaM Unit from do
  assertCanon "prop.empty" (← relationalize (mkConst ``neverVal))
    "Never|mk\nrel[Never,Q,Q]:"

#eval show MetaM Unit from do
  assertCanon "prop.undecidable" (← relationalize (mkConst ``undecVal))
    "Undec|mk\nQ → Prop|λ q\np[Undec,Q → Prop]:0,1"

/-! ### A set is the same table

`Decidable` does not synthesize through an `Insert`/`Singleton` literal's
residual membership, so a set written as a literal stays a leaf. -/

@[expose] public def Set (α : Type) : Type := α → Prop

public instance : Membership α (Set α) := ⟨fun s a => s a⟩
public instance : Singleton α (Set α) := ⟨fun a x => x = a⟩
public instance : Insert α (Set α) := ⟨fun a s x => x = a ∨ x ∈ s⟩

public structure NA where
  accept : Set Q

public def naVal : NA := { accept := fun q => q = Q.q0 ∨ q = Q.q2 }

public structure NALit where
  accept : Set Q

public def naLitVal : NALit := { accept := {Q.q0, Q.q2} }

#eval show MetaM Unit from do
  assertCanon "prop.set" (← relationalize (mkConst ``naVal))
    "NA|mk\nQ|q0\nQ|q2\naccept[NA,Q]:0,1;0,2"

#eval show MetaM Unit from do
  assertCanon "prop.set.literal" (← relationalize (mkConst ``naLitVal))
    "NALit|mk\nQ → Prop|insert\naccept[NALit,Set Q]:0,1"

/-! ## An empty domain registers the relation -/

public structure EmptyDom where
  f : Empty → Nat
  g : Empty → Prop

public def emptyDomVal : EmptyDom := { f := fun e => e.elim, g := fun e => e.elim }

#eval show MetaM Unit from do
  assertCanon "table.emptydom" (← relationalize (mkConst ``emptyDomVal))
    "EmptyDom|mk\nf[EmptyDom,Empty,Nat]:\ng[EmptyDom,Empty]:"

/-! ## Identity decides whether a domain value and a result are one atom -/

public inductive QI where | q0 | q1 | q2
  deriving DecidableEq, SpytialIdentity

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

public structure PropRelI where
  rel : QI → QI → Prop

public def propRelIVal : PropRelI :=
  { rel := fun a b => a = b ∨ (a = QI.q0 ∧ b = QI.q2) }

#eval show MetaM Unit from do
  assertCanon "table.identity" (← relationalize (mkConst ``daiVal))
    "DAI|mk\nQI|q0\nQI|q1\nQI|q2\nBool|false\nBool|true\ntr[DAI,QI,Bool,QI]:0,1,4,1;0,1,5,2;0,2,4,3;0,2,5,1;0,3,4,2;0,3,5,3"

#eval show MetaM Unit from do
  assertCanon "prop.identity" (← relationalize (mkConst ``propRelIVal))
    "PropRelI|mk\nQI|q0\nQI|q2\nQI|q1\nrel[PropRelI,QI,QI]:0,1,1;0,1,2;0,3,3;0,2,2"

/-! ## A DA reaches its table through its parent subobject: `tr`'s owner column
is the subobject atom. The `Fin` instance is derived here, not above, so
`table.fin` stays unmerged. -/

deriving instance SpytialIdentity for Fin

public structure FLTS (State Label : Type) where
  tr : State → Label → State

public structure SubDA (State Symbol : Type) extends FLTS State Symbol where
  start : State

public def subDAFin : SubDA (Fin 3) Bool where
  tr
    | 0, false => 0
    | 0, true  => 1
    | 1, false => 1
    | 1, true  => 2
    | 2, false => 2
    | 2, true  => 0
  start := 0

#eval show MetaM Unit from do
  assertCanon "table.subobject" (← relationalize (mkConst ``subDAFin))
    "SubDA|mk\nFLTS|mk\nFin|mk\nNat|0\nFin|mk\nNat|1\nFin|mk\nNat|2\nBool|false\nBool|true\nstart[SubDA,Fin]:0,2\ntoFLTS[SubDA,FLTS]:0,1\ntr[FLTS,Fin,Bool,Fin]:1,2,8,2;1,2,9,4;1,4,8,4;1,4,9,6;1,6,8,6;1,6,9,2\nval[Fin,Nat]:2,3;4,5;6,7"

#eval show MetaM Unit from do
  assertMatchesReference "diff.table.bool" (mkConst ``boolFVal)
  assertMatchesReference "diff.table.enum" (mkConst ``qStepVal)
  assertMatchesReference "diff.table.fin" (mkConst ``finFVal)
  assertMatchesReference "diff.table.product" (mkConst ``daVal)
  assertMatchesReference "diff.table.cap" (mkConst ``daVal) { maxTableTuples := 3 }
  assertMatchesReference "diff.table.maps" (mkConst ``parity)
  assertMatchesReference "diff.table.identity" (mkConst ``daiVal)
  assertMatchesReference "diff.table.root" (← boolLam)
  assertMatchesReference "diff.prop.table" (mkConst ``propRelVal)
  assertMatchesReference "diff.prop.sparse" (mkConst ``sparseVal)
  assertMatchesReference "diff.prop.empty" (mkConst ``neverVal)
  assertMatchesReference "diff.table.emptydom" (mkConst ``emptyDomVal)
  assertMatchesReference "diff.prop.set" (mkConst ``naVal)
  assertMatchesReference "diff.prop.identity" (mkConst ``propRelIVal)
  assertMatchesReference "diff.table.subobject" (mkConst ``subDAFin)

/-! ## A `Prop` behind a definition still tabulates — `Decidable (Linked a b)`
matches nothing until `Linked` unfolds. -/

public def Linked (a b : Bool) : Prop := a = b

public structure Boxed where
  rel : Bool → Bool → Prop

public def boxed : Boxed := { rel := fun a b => Linked a b }

#eval show Lean.Elab.TermElabM Unit from do
  assertCanon "prop.behind.def" (← relationalize (mkConst ``boxed))
    "Boxed|mk\nBool|false\nBool|true\nrel[Boxed,Bool,Bool]:0,1,1;0,2,2"

/-! ## A field name outside Lean's identifier alphabet: the guillemets are
source syntax, not part of the name, so the relation is `∈`. -/

public structure SMem where
  «∈» : Nat

public def sMemVal : SMem := { «∈» := 1 }

#eval show MetaM Unit from do
  assertCanon "field.symbolic" (← relationalize (mkConst ``sMemVal))
    "SMem|mk\nNat|1\n∈[SMem,Nat]:0,1"

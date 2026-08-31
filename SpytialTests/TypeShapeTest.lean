module

public import SpytialLean.Enum
meta import SpytialLean.TypeShape
meta import SpytialLean.Relationalizer

open SpytialLean Lean Meta

private meta def assertEq {α} [BEq α] [Repr α] (label : String) (got expected : Array α) :
    MetaM Unit := do
  unless got == expected do
    throwError "{label}: got {toString (repr got)}, expected {toString (repr expected)}"

#eval show MetaM Unit from do
  assertEq "shortName.str"  #[shortName `Foo.Bar.baz] #["baz"]
  assertEq "shortName.flat" #[shortName `baz] #["baz"]
  assertEq "shortName.anon" #[shortName Name.anonymous] #["_"]
  assertEq "shortName.num"  #[shortName (Name.num `Foo 3)] #["3"]
  assertEq "rel.named"  #[fieldRelName "node" #[`left, `right] 0] #["left"]
  assertEq "rel.named2" #[fieldRelName "node" #[`left, `right] 1] #["right"]
  assertEq "rel.oob"    #[fieldRelName "node" #[`left, `right] 2] #["node_2"]
  assertEq "rel.anon"   #[fieldRelName "mk" #[Name.anonymous] 0] #["mk_0"]
  assertEq "rel.empty"  #[fieldRelName "mk" #[] 5] #["mk_5"]

public inductive Tree (α : Type) where
  | leaf (value : α)
  | node (left right : Tree α)

public inductive Pos where
  | mk : Nat → Nat → Pos

public structure Demo where
  val : Nat
  ok : val = val

#eval show MetaM Unit from do
  let some ts ← TypeShape.ofInductive ``Tree | throwError "Tree: no shape"
  assertEq "Tree.sig"          #[ts.sig] #["Tree"]
  assertEq "Tree.ctors"        (ts.ctors.map (·.ctorShort)) #["leaf", "node"]
  assertEq "Tree.dataRelNames" ts.dataRelNames #["value", "left", "right"]
  assertEq "Tree.leaf.typeSig" (ts.ctors[0]!.fields.map (·.typeSig)) #[none]
  assertEq "Tree.node.typeSig" (ts.ctors[1]!.fields.map (·.typeSig)) #[some "Tree", some "Tree"]
  assertEq "Tree.leaf.typeHead" (ts.ctors[0]!.fields.map (·.typeHead)) #[none]
  assertEq "Tree.node.typeHead" (ts.ctors[1]!.fields.map (·.typeHead)) #[some ``Tree, some ``Tree]

#eval show MetaM Unit from do
  let some ts ← TypeShape.ofInductive ``Pos | throwError "Pos: no shape"
  assertEq "Pos.dataRelNames" ts.dataRelNames #["mk_0", "mk_1"]

#eval show MetaM Unit from do
  let some ts ← TypeShape.ofInductive ``Demo | throwError "Demo: no shape"
  let mk := ts.ctors[0]!
  assertEq "Demo.relNames"     (mk.fields.map (·.relName)) #["val", "ok"]
  assertEq "Demo.isProofLike"  (mk.fields.map (·.isProofLike)) #[false, true]
  assertEq "Demo.dataRelNames" ts.dataRelNames #["val"]

public structure Bundle where
  carrier : Type
  size : Nat

#eval show MetaM Unit from do
  let some ts ← TypeShape.ofInductive ``Bundle | throwError "Bundle: no shape"
  let mk := ts.ctors[0]!
  assertEq "Bundle.relNames"     (mk.fields.map (·.relName)) #["carrier", "size"]
  assertEq "Bundle.isProofLike"  (mk.fields.map (·.isProofLike)) #[true, false]
  assertEq "Bundle.typeHead"     (mk.fields.map (·.typeHead)) #[none, some ``Nat]
  assertEq "Bundle.dataRelNames" ts.dataRelNames #["size"]

#eval show MetaM Unit from do
  let r ← TypeShape.ofInductive ``Nat.add
  unless r.isNone do throwError "expected none for a non-inductive"

/-! ## Hole labels -/

#eval show MetaM Unit from do
  assertEq "hole.anon"  #[holeLabel Name.anonymous] #["?"]
  assertEq "hole.named" #[holeLabel `subtree] #["?subtree"]
  assertEq "hyp.named"  #[hypLabel `t] #["t"]
  assertEq "hyp.anon"   #[hypLabel Name.anonymous] #["?"]
  let hygienic ← Lean.Core.mkFreshUserName `x
  assertEq "hole.scoped" #[holeLabel hygienic] #["?"]
  assertEq "hyp.scoped"  #[hypLabel hygienic] #["x"]

/-! ## Walker: open values (holes and hypotheses) -/

#eval show MetaM Unit from do
  let treeNat := mkApp (mkConst ``Tree) (mkConst ``Nat)
  let hole ← mkFreshExprMVar (some treeNat)
  let di ← relationalize hole
  assertEq "mvar.labels" (di.atoms.map (·.label)) #["?"]
  assertEq "mvar.types"  (di.atoms.map (·.type))  #["Tree"]
  let named ← mkFreshExprMVar (some treeNat) (userName := `subtree)
  let di ← relationalize named
  assertEq "mvar.named.labels" (di.atoms.map (·.label)) #["?subtree"]
  withLocalDeclD `t treeNat fun t => do
    let di ← relationalize t
    assertEq "fvar.labels" (di.atoms.map (·.label)) #["t"]
    assertEq "fvar.types"  (di.atoms.map (·.type))  #["Tree"]

#eval show MetaM Unit from do
  let treeNat := mkApp (mkConst ``Tree) (mkConst ``Nat)
  let leaf1 := mkApp2 (mkConst ``Tree.leaf) (mkConst ``Nat) (mkRawNatLit 1)
  let hole ← mkFreshExprMVar (some treeNat)
  let di ← relationalize (mkApp3 (mkConst ``Tree.node) (mkConst ``Nat) leaf1 hole)
  assertEq "partial.labels" (di.atoms.map (·.label)) #["node", "leaf", "1", "?"]
  assertEq "partial.rels"   ((di.relations.map (·.name)).qsort (· < ·)) #["left", "right", "value"]
  -- the *same* hole twice is one atom: filling it fills both slots
  let di ← relationalize (mkApp3 (mkConst ``Tree.node) (mkConst ``Nat) hole hole)
  assertEq "shared-hole.labels" (di.atoms.map (·.label)) #["node", "?"]

/-! ## Walker: stuck match -/

#eval show Lean.Elab.TermElabM Unit from do
  let treeNat := mkApp (mkConst ``Tree) (mkConst ``Nat)
  withLocalDeclD `t treeNat fun t => do
    let tStx ← Lean.Elab.Term.exprToSyntax t
    let stx ← `(match $tStx:term with | .leaf v => v | .node _ _ => 0)
    let e ← Lean.Elab.Term.elabTermEnsuringType stx (some (mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let di ← relationalize e
    assertEq "match.labels" (di.atoms.map (·.label)) #["match", "0", "t"]
    assertEq "match.types"  (di.atoms.map (·.type))  #["Nat", "Nat", "Tree"]
    assertEq "match.rels"   (di.relations.map (·.name)) #["scrutinee"]

#eval show Lean.Elab.TermElabM Unit from do
  let treeNat := mkApp (mkConst ``Tree) (mkConst ``Nat)
  withLocalDeclD `t treeNat fun t => do
  withLocalDeclD `u treeNat fun u => do
    let tStx ← Lean.Elab.Term.exprToSyntax t
    let uStx ← Lean.Elab.Term.exprToSyntax u
    let stx ← `(match $tStx:term, $uStx:term with | .leaf v, _ => v | _, _ => 0)
    let e ← Lean.Elab.Term.elabTermEnsuringType stx (some (mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let di ← relationalize e
    assertEq "match2.labels" (di.atoms.map (·.label)) #["match", "0", "t", "1", "u"]
    assertEq "match2.rels"   (di.relations.map (·.name)) #["scrutinee"]

/-! ## `SpytialEnum` domains, derived on demand — no `deriving` clause below -/

public structure Win where
  prev : Bool
  cur : Bool

public inductive Rec where
  | nil
  | step (r : Rec)

public structure Tagged where
  tag : String
  on : Bool

#eval show Lean.Elab.TermElabM Unit from do
  let check (label : String) (b : Bool) : Lean.Elab.TermElabM Unit :=
    unless b do throwError "{label}"
  let some win ← tryEnumerateDomain (mkConst ``Win) | throwError "Win did not enumerate"
  check "enum.struct.count" (win.size == 4)
  let some bools ← tryEnumerateDomain (mkConst ``Bool) | throwError "Bool did not enumerate"
  assertEq "enum.bool.labels" (bools.map (·.1)) #["false", "true"]
  let some pair ← tryEnumerateDomain (← mkAppM ``Prod #[mkConst ``Bool, mkConst ``Win])
    | throwError "Bool x Win did not enumerate"
  check "enum.prod.count" (pair.size == 8)
  check "enum.recursive" (← tryEnumerateDomain (mkConst ``Rec)).isNone
  check "enum.nat" (← tryEnumerateDomain (mkConst ``Nat)).isNone
  check "enum.string" (← tryEnumerateDomain (mkConst ``String)).isNone
  check "enum.tagged" (← tryEnumerateDomain (mkConst ``Tagged)).isNone

-- separate command: the stale instance cache hides the sorryAx until a fresh synthInstance?
#eval show MetaM Unit from do
  unless (← Meta.synthInstance? (← mkAppM ``SpytialEnum #[mkConst ``Tagged])).isNone do
    throwError "the refused `Tagged` derive left an instance behind"

-- maxRecDepth fires before enumFuel; Fin 600 first to pin that the abort is non-fatal
#eval show Lean.Elab.TermElabM Unit from do
  let fin (n : Nat) := mkApp (mkConst ``Fin) (mkNatLit n)
  unless (← tryEnumerateDomain (fin 600)).isNone do throwError "Fin 600 did not decline"
  let some narrow ← tryEnumerateDomain (fin 100) | throwError "Fin 100 did not enumerate"
  unless narrow.size == 100 do throwError "Fin 100 listed {narrow.size} elements"

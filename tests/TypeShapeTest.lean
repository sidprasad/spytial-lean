module

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
  | mk : Nat → Nat → Pos          -- positional (anonymous) fields → fallback names

public structure Demo where
  val : Nat
  ok : val = val                  -- a Prop field, filtered from data relations

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
  carrier : Type                  -- a Sort-typed field: proof-like, dropped by the walker
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

/-! ## Walker: stuck match

Elaborated here exactly as a synthesized term containing `match` would be. -/

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

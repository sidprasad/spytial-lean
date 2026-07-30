module

meta import SpytialLean.TypeShape

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

public structure Pack where
  items : List (Tree Nat)             -- container: element vocabulary, recursively
  bound : Fin 3                       -- value argument: contributes nothing
  size : Nat

#eval show MetaM Unit from do
  let some ts ← TypeShape.ofInductive ``Pack | throwError "Pack: no shape"
  let mk := ts.ctors[0]!
  assertEq "Pack.typeHead"     (mk.fields.map (·.typeHead)) #[some ``List, some ``Fin, some ``Nat]
  assertEq "Pack.typeArgHeads" (mk.fields.map (·.typeArgHeads)) #[#[``Tree, ``Nat], #[], #[]]

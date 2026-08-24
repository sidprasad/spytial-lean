module

public import SpytialLean.Identity
meta import SpytialLean.Identity
public meta import SpytialLean.MetaEncode
public meta import SpytialLean.Relationalizer
meta import SpytialLean.Command
meta import WalkCanon

open SpytialLean Lean Meta

private meta def assertEq {α} [BEq α] [Repr α] (label : String) (got expected : Array α) :
    MetaM Unit := do
  unless got == expected do
    throwError "{label}: got {toString (repr got)}, expected {toString (repr expected)}"

private meta def assert (label : String) (b : Bool) : MetaM Unit := do
  unless b do throwError "{label}: assertion failed"

/-! ## Fixtures

`WTree` opts in to derived structural identity; `UTree` is its identical twin
with no clause, so it takes the derive-on-demand default. `OTree` below is the
as-written control. -/

public inductive WTree where
  | leaf (n : Nat)
  | node (l r : WTree)
  deriving SpytialIdentity

public inductive UTree where
  | leaf (n : Nat)
  | node (l r : UTree)

/-- The same shape, declining the derive-on-demand default. -/
public inductive OTree where
  | leaf (n : Nat)
  | node (l r : OTree)

public instance : SpytialIdentity OTree := SpytialIdentity.asWritten

/-- Derived over an `asWritten` field. `Holder` keeps merging arms of its own,
    so it cannot present `asWritten`; it degrades to `.eqv` with a decider that
    is false on `hold` and true on `stump`. -/
public inductive Holder where
  | stump
  | hold (t : OTree)
  | both (a b : Holder)

/-- Parity: a genuinely relational (`.eqv`) identity. -/
public structure ModTwo where
  n : Nat

instance : SpytialIdentity ModTwo := ⟨.eqv (fun a b => a.n % 2 == b.n % 2), none⟩

/-- Underived container: children consult their own types (node-local default). -/
public structure Trio where
  a : ModTwo
  b : ModTwo
  c : ModTwo

/-- Derived over an encoded (`List Nat`) field: the field routes through the
    lifted `ToIdentityKey` encoding, meta-side and runtime alike. -/
public structure Sack where
  items : List Nat
  deriving SpytialIdentity

/-- Derived over `Bool`/`Int`/`Option String` encodings. -/
public structure Mixed where
  flag : Bool
  count : Int
  name : Option String
  deriving SpytialIdentity

/-- Deliberate opacity: keys by its spelling, never by its unfolding. -/
@[irreducible] public def hiddenTree : WTree := .node (.leaf 1) (.leaf 1)

/-! ## Expr builders (headless, like the TypeShape walker tests) -/

private meta def wleaf (n : Nat) : Expr := mkApp (mkConst ``WTree.leaf) (mkRawNatLit n)
private meta def wnode (l r : Expr) : Expr := mkApp2 (mkConst ``WTree.node) l r
private meta def uleaf (n : Nat) : Expr := mkApp (mkConst ``UTree.leaf) (mkRawNatLit n)
private meta def unode (l r : Expr) : Expr := mkApp2 (mkConst ``UTree.node) l r
private meta def oleaf (n : Nat) : Expr := mkApp (mkConst ``OTree.leaf) (mkRawNatLit n)
private meta def onode (l r : Expr) : Expr := mkApp2 (mkConst ``OTree.node) l r
private meta def hold (t : Expr) : Expr := mkApp (mkConst ``Holder.hold) t
private meta def hboth (a b : Expr) : Expr := mkApp2 (mkConst ``Holder.both) a b
private meta def mod2 (n : Nat) : Expr := mkApp (mkConst ``ModTwo.mk) (mkRawNatLit n)
private meta def trio (a b c : Expr) : Expr := mkApp3 (mkConst ``Trio.mk) a b c

private meta unsafe def evalKeyOptUnsafe (e : Expr) : MetaM (Option IdentityKey) :=
  Meta.evalExpr (Option IdentityKey)
    (mkApp (mkConst ``Option [.zero]) (mkConst ``IdentityKey)) e

@[implemented_by evalKeyOptUnsafe]
private meta opaque evalKeyOpt (e : Expr) : MetaM (Option IdentityKey)

/-- The walker's meta-side structural key must equal the compiled derived
    classifier's key, byte for byte. -/
private meta def checkMetaMatchesRuntime (label : String) (val : Expr) : MetaM Unit := do
  let (mk?, _) ← (structuralKey? val).run {}
  let some mkey := mk? | throwError "{label}: meta-side key not computed"
  let some rkey ← evalKeyOpt (← mkAppM ``SpytialIdentity.runtimeKey? #[val])
    | throwError "{label}: runtime classifier absent"
  unless mkey == rkey do
    throwError "{label}: meta key {repr mkey} ≠ runtime key {repr rkey}"

/-! ## Derive-on-demand default: no clause ⇒ equal subterms merge. `asWritten`
declines, node-locally — the `Nat` children keep consulting their own type,
which is what separates it from a `Raw` region. -/

#eval show MetaM Unit from do
  let di ← relationalize (unode (uleaf 1) (uleaf 1))
  assertEq "autoderive.labels" (di.atoms.map (·.label)) #["node", "leaf", "1"]

#eval show MetaM Unit from do
  let di ← relationalize (onode (oleaf 1) (oleaf 1))
  assertEq "aswritten.labels" (di.atoms.map (·.label)) #["node", "leaf", "1", "leaf"]

/-! An `asWritten` field disqualifies the constructors that carry it, and only
those: the composite's decider is non-reflexive exactly there, so the walker's
exact-spelling shortcut must not fire. -/

#eval show MetaM Unit from do
  let di ← relationalize (hboth (hold (oleaf 1)) (hold (oleaf 1)))
  assertEq "aswritten.field.labels" (di.atoms.map (·.label))
    #["both", "hold", "leaf", "1", "hold", "leaf"]

#eval show MetaM Unit from do
  let di ← relationalize (hboth (mkConst ``Holder.stump) (mkConst ``Holder.stump))
  assertEq "aswritten.field.other-arms" (di.atoms.map (·.label)) #["both", "stump"]

/-! ## Derived structural identity: sharing, and the A/B example

`node (leaf 1) (leaf 1)` and `node (leaf 1) (leaf (0+1))` are the same value;
they draw one picture, with the equal leaves shared. -/

#eval show MetaM Unit from do
  let A := wnode (wleaf 1) (wleaf 1)
  let B := wnode (wleaf 1) (mkApp (mkConst ``WTree.leaf)
    (mkApp2 (mkConst ``Nat.add) (mkRawNatLit 0) (mkRawNatLit 1)))
  let diA ← relationalize A
  assertEq "derived.labels" (diA.atoms.map (·.label)) #["node", "leaf", "1"]
  let diB ← relationalize B
  assert "chimera.same-picture" (canonInstance diA == canonInstance diB)

#eval show MetaM Unit from do
  checkMetaMatchesRuntime "xcheck.wtree" (wnode (wleaf 1) (wleaf 2))
  checkMetaMatchesRuntime "xcheck.sack"
    (mkApp (mkConst ``Sack.mk) (toExpr ([1, 2] : List Nat)))
  checkMetaMatchesRuntime "xcheck.mixed"
    (mkApp3 (mkConst ``Mixed.mk) (toExpr true) (toExpr (-3 : Int))
      (toExpr (some "hi" : Option String)))

/-! ## Encoding twins: every `MetaEncode` instance cross-checks byte-for-byte

The enumeration keeps coverage honest: a twin without a sample here fails the
build. -/

private meta def checkTwin {α : Type} [ToIdentityKey α] [MetaEncode α]
    (label : String) (e : Expr) (v : α) : MetaM Unit := do
  let some mk ← MetaEncode.keyOf? α e
    | throwError "{label}: twin failed on a literal"
  let rk := ToIdentityKey.toKey v
  unless mk == rk do
    throwError "{label}: twin {repr mk} ≠ toKey {repr rk}"

private meta def uintE (ofNat : Name) (n : Nat) : Expr :=
  mkApp (mkConst ofNat) (toExpr n)

#eval show MetaM Unit from do
  MetaEncode.check "twin.nat" (3 : Nat)
  MetaEncode.check "twin.string" "leaf"
  MetaEncode.check "twin.bool.t" true
  MetaEncode.check "twin.bool.f" false
  MetaEncode.check "twin.char" 'a'
  MetaEncode.check "twin.int.pos" (3 : Int)
  MetaEncode.check "twin.int.neg" (-3 : Int)
  checkTwin "twin.uint8" (uintE ``UInt8.ofNat 5) (5 : UInt8)
  checkTwin "twin.uint16" (uintE ``UInt16.ofNat 5) (5 : UInt16)
  checkTwin "twin.uint32" (uintE ``UInt32.ofNat 5) (5 : UInt32)
  checkTwin "twin.uint64" (uintE ``UInt64.ofNat 5) (5 : UInt64)
  MetaEncode.check "twin.list" ([1, 2] : List Nat)
  MetaEncode.check "twin.array" (#[1, 2] : Array Nat)
  MetaEncode.check "twin.option.some" (some 1 : Option Nat)
  MetaEncode.check "twin.option.none" (none : Option Nat)
  MetaEncode.check "twin.prod" ((1, "a") : Nat × String)

private meta def sampledHeads : NameSet :=
  ([``Nat, ``String, ``Bool, ``Char, ``Int, ``UInt8, ``UInt16, ``UInt32,
    ``UInt64, ``List, ``Array, ``Option, ``Prod] : List Name)
    |>.foldl (·.insert ·) {}

#eval show MetaM Unit from do
  let env ← getEnv
  for (instName, _) in (Meta.instanceExtension.getState env).instanceNames.toList do
    let info ← getConstInfo instName
    let head? ← forallTelescopeReducing info.type fun _ b =>
      pure (if b.isApp && b.getAppFn.constName? == some ``MetaEncode
            then b.appArg!.getAppFn.constName? else none)
    if let some h := head? then
      unless sampledHeads.contains h do
        throwError "MetaEncode instance for '{h}' has no cross-check sample — add one above"

/-! ## Eval fallback: a meta miss costs an evaluation, never the merge

A hand-written encoding without a twin, and a field whose instance is a user
classifier: both make the generated twin miss, and the walker falls back to
the compiled classifier. -/

public structure Coupon where
  code : String

public instance : ToIdentityKey Coupon where
  toKey c := .ofList [.ofString "coupon", .ofString c.code]

public structure Wallet where
  c : Coupon
  deriving SpytialIdentity

public structure WPair where
  l : Wallet
  r : Wallet
  deriving SpytialIdentity

public structure Chosen where
  n : Nat

public instance : SpytialIdentity Chosen := ⟨.identity fun c => .ofNat (c.n % 2), none⟩

public structure CBox where
  x : Chosen
  deriving SpytialIdentity

public structure CPair where
  a : CBox
  b : CBox
  deriving SpytialIdentity

#eval show MetaM Unit from do
  let w := mkApp (mkConst ``Wallet.mk) (mkApp (mkConst ``Coupon.mk) (toExpr "a"))
  let (k?, _) ← (structuralKey? w).run {}
  assert "fallback.twin-misses" k?.isNone
  let di ← relationalize (mkApp2 (mkConst ``WPair.mk) w w)
  assertEq "fallback.encoding.merged" (di.atoms.map (·.label)) #["mk", "mk", "mk", "\"a\""]

#eval show MetaM Unit from do
  let c1 := mkApp (mkConst ``CBox.mk) (mkApp (mkConst ``Chosen.mk) (toExpr (1 : Nat)))
  let c3 := mkApp (mkConst ``CBox.mk) (mkApp (mkConst ``Chosen.mk) (toExpr (3 : Nat)))
  -- Chosen's classifier maps 1 and 3 alike; meta cannot run it, the fallback can
  let di ← relationalize (mkApp2 (mkConst ``CPair.mk) c1 c3)
  assertEq "fallback.classifier.merged" (di.atoms.map (·.label)) #["mk", "mk", "mk", "1"]

/-! ## `.eqv`: groups form by the declared relation; order changes the drawn
representative, never the partition -/

#eval show MetaM Unit from do
  let di ← relationalize (trio (mod2 1) (mod2 3) (mod2 2))
  -- 1 and 3 are one parity group (the first occurrence is drawn); 2 is its own
  assertEq "eqv.labels" (di.atoms.map (·.label)) #["mk", "mk", "1", "mk", "2"]
  let di2 ← relationalize (trio (mod2 3) (mod2 1) (mod2 2))
  assertEq "eqv.perm.labels" (di2.atoms.map (·.label)) #["mk", "mk", "3", "mk", "2"]
  assert "eqv.perm.partition" (di.atoms.size == di2.atoms.size)

/-! ## Modes: `Raw` draws as written, `Viewed` shifts back, holes are holes
everywhere -/

#eval show MetaM Unit from do
  let A := wnode (wleaf 1) (wleaf 1)
  let di ← relationalize (← mkAppM ``Raw.mk #[A])
  assertEq "raw.labels" (di.atoms.map (·.label)) #["node", "leaf", "1", "leaf", "1"]
  assert "raw.no-wrapper-atom" (di.atoms.all (·.type != "Raw"))
  let di ← relationalize (← mkAppM ``Viewed.mk #[← mkAppM ``Raw.mk #[A]])
  -- innermost wrapper wins: Viewed (Raw _) still draws as written
  assertEq "viewed-raw.labels" (di.atoms.map (·.label)) #["node", "leaf", "1", "leaf", "1"]
  let di ← relationalize (← mkAppM ``Raw.mk #[← mkAppM ``Viewed.mk #[A]])
  assertEq "raw-viewed.labels" (di.atoms.map (·.label)) #["node", "leaf", "1"]

#eval show MetaM Unit from do
  let hole ← mkFreshExprMVar (some (mkConst ``WTree))
  let di ← relationalize (← mkAppM ``Raw.mk #[wnode hole hole])
  assertEq "raw.shared-hole" (di.atoms.map (·.label)) #["node", "?"]

/-! ## Opacity: deliberately-stuck heads key by spelling -/

#eval show MetaM Unit from do
  let hidden := mkConst ``hiddenTree
  let di ← relationalize (← mkAppM ``Prod.mk #[hidden, hidden])
  -- two occurrences of the same spelling are one atom …
  assertEq "opaque.merged" (di.atoms.map (·.label)) #["mk", "hiddenTree"]
  -- … and the spelling never merges with the unfolding it refuses to expose
  let di ← relationalize (← mkAppM ``Prod.mk #[hidden, wnode (wleaf 1) (wleaf 1)])
  assertEq "opaque.vs-literal" (di.atoms.map (·.label))
    #["mk", "hiddenTree", "node", "leaf", "1"]

/-! ## Opacity survives namespacing and composites

Two regressions. The twin must register under the name it actually elaborated
to — a `namespace` around the type used to kill the meta lane. And
`viaOf`/`classifier?` must stay whnf-able from module contexts — a composite's
`via` match used to get stuck and degrade the route to `.eqvRel`. Either way
the compiled classifier runs, unfolds the irreducible head, and merges it with
its unfolding. -/

namespace NsReg
public inductive NTree where
  | leaf (n : Nat)
  | node (l r : NTree)
  deriving SpytialIdentity

@[irreducible] public def hiddenN : NTree := .node (.leaf 1) (.leaf 1)
end NsReg

#eval show MetaM Unit from do
  let lit := mkApp2 (mkConst ``NsReg.NTree.node)
    (mkApp (mkConst ``NsReg.NTree.leaf) (mkRawNatLit 1))
    (mkApp (mkConst ``NsReg.NTree.leaf) (mkRawNatLit 1))
  let di ← relationalize (← mkAppM ``Prod.mk #[mkConst ``NsReg.hiddenN, lit])
  assertEq "opaque.namespaced" (di.atoms.map (·.label))
    #["mk", "NsReg.hiddenN", "node", "leaf", "1"]

public structure WHolder where
  t : WTree
  deriving SpytialIdentity

#eval show MetaM Unit from do
  let h1 := mkApp (mkConst ``WHolder.mk) (mkConst ``hiddenTree)
  let h2 := mkApp (mkConst ``WHolder.mk) (wnode (wleaf 1) (wleaf 1))
  let di ← relationalize (← mkAppM ``Prod.mk #[h1, h2])
  assertEq "opaque.composite" (di.atoms.map (·.label))
    #["mk", "mk", "hiddenTree", "mk", "node", "leaf", "1"]

/-! ## Custom relationalizer wins over any identity instance -/

public structure Boxy where
  n : Nat
  deriving SpytialIdentity

public meta def boxyRel : CustomRelationalizer := fun _ _ => do
  modify fun s : WalkState => s.addAtom { id := "boxy", type := "Boxy", label := "boxy!" }
  return "boxy"

spytial_relationalizer Boxy boxyRel

#eval show MetaM Unit from do
  let b := mkApp (mkConst ``Boxy.mk) (mkRawNatLit 1)
  let di ← relationalize (← mkAppM ``Prod.mk #[b, b])
  -- the relationalizer's rendering, not the derived structural one — and the
  -- repeated occurrence reconciles to the id it actually returned
  assertEq "custom.labels" (di.atoms.map (·.label)) #["mk", "boxy!"]

/-! ## Differential oracle: the fused walker equals the two-pass reference -/

#eval show MetaM Unit from do
  let A := wnode (wleaf 1) (wleaf 1)
  let B := wnode (wleaf 1) (mkApp (mkConst ``WTree.leaf)
    (mkApp2 (mkConst ``Nat.add) (mkRawNatLit 0) (mkRawNatLit 1)))
  assertMatchesReference "diff.aswritten" (unode (uleaf 1) (uleaf 1))
  assertMatchesReference "diff.aswritten.field" (hboth (hold (oleaf 1)) (hold (oleaf 1)))
  assertMatchesReference "diff.derived" A
  assertMatchesReference "diff.chimera" B
  assertMatchesReference "diff.deep"
    (wnode (wnode (wleaf 1) (wleaf 1)) (wnode (wleaf 1) (wleaf 1)))
  assertMatchesReference "diff.sack"
    (mkApp (mkConst ``Sack.mk) (toExpr ([1, 2] : List Nat)))
  assertMatchesReference "diff.mixed"
    (mkApp3 (mkConst ``Mixed.mk) (toExpr true) (toExpr (-3 : Int))
      (toExpr (some "hi" : Option String)))
  assertMatchesReference "diff.eqv" (trio (mod2 1) (mod2 3) (mod2 2))
  assertMatchesReference "diff.eqv.perm" (trio (mod2 3) (mod2 1) (mod2 2))
  assertMatchesReference "diff.raw" (← mkAppM ``Raw.mk #[A])
  assertMatchesReference "diff.raw-viewed"
    (← mkAppM ``Raw.mk #[← mkAppM ``Viewed.mk #[A]])
  assertMatchesReference "diff.opaque"
    (← mkAppM ``Prod.mk #[mkConst ``hiddenTree, mkConst ``hiddenTree])
  assertMatchesReference "diff.custom"
    (← mkAppM ``Prod.mk #[mkApp (mkConst ``Boxy.mk) (mkRawNatLit 1),
                          mkApp (mkConst ``Boxy.mk) (mkRawNatLit 1)])
  let hole ← mkFreshExprMVar (some (mkConst ``WTree))
  assertMatchesReference "diff.hole" (wnode (wleaf 1) hole)

/-! ## Parametric and mutual twins, the type half of the atom-table key, and
shadowing -/

inductive PL (α : Type) where
  | pnil
  | pcons (h : α) (t : PL α)
  deriving SpytialIdentity

mutual
  inductive MEv where
    | mnilE
    | mconsE (n : Nat) (t : MOd)
  inductive MOd where
    | mconsO (n : Nat) (t : MEv)
end

deriving instance SpytialIdentity for MEv, MOd

structure KA where
  n : Nat
  deriving SpytialIdentity

structure KB where
  n : Nat
  deriving SpytialIdentity

#eval show MetaM Unit from do
  let pnilE := mkApp (mkConst ``PL.pnil) (mkConst ``WTree)
  let pcons (h t : Expr) := mkApp3 (mkConst ``PL.pcons) (mkConst ``WTree) h t
  checkMetaMatchesRuntime "xcheck.parametric" (pcons (wleaf 1) (pcons (wleaf 2) pnilE))
  checkMetaMatchesRuntime "xcheck.mutual"
    (mkApp2 (mkConst ``MEv.mconsE) (mkRawNatLit 1)
      (mkApp2 (mkConst ``MOd.mconsO) (mkRawNatLit 2) (mkConst ``MEv.mnilE)))
  -- equal keys, distinct types: the type half of the atom-table key keeps them apart
  let ka := mkApp (mkConst ``KA.mk) (mkRawNatLit 1)
  let kb := mkApp (mkConst ``KB.mk) (mkRawNatLit 1)
  let di ← relationalize (← mkAppM ``Prod.mk #[ka, kb])
  assertEq "typekey.types" (di.atoms.map (·.type)) #["Prod", "KA", "Nat", "KB"]

/-! Shadowing a derived instance: the shadow wins coherently — the route is an
ordinary classifier, and the twin is never consulted. -/

structure ShFoo where
  n : Nat
  deriving SpytialIdentity

instance (priority := high) : SpytialIdentity ShFoo :=
  ⟨.identity fun _ => .ofString "all", none⟩

#eval show MetaM Unit from do
  let f1 := mkApp (mkConst ``ShFoo.mk) (mkRawNatLit 1)
  let f2 := mkApp (mkConst ``ShFoo.mk) (mkRawNatLit 2)
  let di ← relationalize (← mkAppM ``Prod.mk #[f1, f2])
  assertEq "shadow.types" (di.atoms.map (·.type)) #["Prod", "ShFoo", "Nat"]

/-! ## Leaf labels through `Repr`: a stuck-but-closed leaf reads as its
evaluated value when its type declares `Repr`; `Repr` never feeds identity -/

@[irreducible] public def opaque97 : Nat := 90 + 7

/-- Declares both `SpytialIdentity` and `Repr`; `hiddenCoin` below is the
    opaque occurrence. Spelling decides identity, `Repr` decides the label. -/
public inductive Coin where
  | heads | tails
  deriving SpytialIdentity, Repr

@[irreducible] public def hiddenCoin : Coin := .heads

#eval show MetaM Unit from do
  let di ← relationalize (mkConst ``opaque97)
  assertEq "leaflabel.repr" (di.atoms.map (·.label)) #["97"]
  -- `Nat` now takes the supplied `ToIdentityKey` default, and the classifier
  -- route evaluates through an `@[irreducible]` head where the structural route
  -- would have keyed by spelling. So an opaque primitive merges by its value:
  -- pinned here because it is a live ruling, not a settled one.
  let di ← relationalize (← mkAppM ``Prod.mk #[mkConst ``opaque97, mkConst ``opaque97])
  assertEq "leaflabel.opaque.evaluated" (di.atoms.map (·.label)) #["mk", "97"]
  let di ← relationalize (← mkAppM ``Prod.mk #[mkConst ``opaque97, mkRawNatLit 97])
  assertEq "leaflabel.opaque.pierced" (di.atoms.map (·.label)) #["mk", "97"]
  -- spelling merges the occurrences, `Repr` labels the one atom
  let di ← relationalize (← mkAppM ``Prod.mk #[mkConst ``hiddenCoin, mkConst ``hiddenCoin])
  assertEq "leaflabel.opaque.merged" (di.atoms.map (·.label)) #["mk", "Coin.heads"]
  let di ← relationalize (mkConst ``hiddenTree)
  assertEq "leaflabel.no-repr" (di.atoms.map (·.label)) #["hiddenTree"]
  assertMatchesReference "diff.leaflabel"
    (← mkAppM ``Prod.mk #[mkConst ``opaque97, mkConst ``opaque97])
  assertMatchesReference "diff.leaflabel.merged"
    (← mkAppM ``Prod.mk #[mkConst ``hiddenCoin, mkConst ``hiddenCoin])

/-! ## Derive-on-demand reaches an applied type's arguments

The generated instance for a parameterized type binds one `[SpytialIdentity _]`
per parameter, so the arguments need instances of their own or nothing merges.
`PSub` is the negative control: its inherited field is a function, so the
generated command fails to elaborate and the derive must restore the
environment. -/

public inductive PTree (α : Type) where
  | leaf (value : α)
  | node (left right : PTree α)

public structure PBox where
  n : Nat

public structure PFn (State Label : Type) where
  tr : State → Label → State

public structure PSub (State Label : Type) extends PFn State Label where
  start : State

private meta def pTreeOf (α : Name) (v : Expr) : Expr :=
  let leaf := mkApp2 (mkConst ``PTree.leaf) (mkConst α) v
  mkApp3 (mkConst ``PTree.node) (mkConst α) leaf leaf

#eval show MetaM Unit from do
  -- an argument whose identity comes from its encoding
  let di ← relationalize (pTreeOf ``Nat (mkRawNatLit 1))
  assertEq "param.encoded" (di.atoms.map (·.label)) #["node", "leaf", "1"]
  -- an argument that has to be derived structurally
  let di ← relationalize (pTreeOf ``PBox (mkApp (mkConst ``PBox.mk) (mkRawNatLit 1)))
  assertEq "param.structural" (di.atoms.map (·.label)) #["node", "leaf", "mk", "1"]
  -- the argument is itself applied
  let inner := mkApp (mkConst ``PTree) (mkConst ``Nat)
  let v := mkApp2 (mkConst ``PTree.leaf) inner
    (mkApp2 (mkConst ``PTree.leaf) (mkConst ``Nat) (mkRawNatLit 1))
  let di ← relationalize (mkApp3 (mkConst ``PTree.node) inner v v)
  assertEq "param.nested" (di.atoms.map (·.label)) #["node", "leaf", "leaf", "1"]

-- a failed derive leaves a sorryAx instance via error recovery
#eval show MetaM Unit from do
  let ty := mkApp2 (mkConst ``PSub) (mkConst ``Bool) (mkConst ``Bool)
  assert "param.refused" ((← deriveIdentity ty) matches .refused _)
  assert "param.no-sorry-instance"
    (← Meta.synthInstance? (← mkAppM ``SpytialIdentity #[ty])).isNone

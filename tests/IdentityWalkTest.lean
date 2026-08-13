module

public import SpytialLean.Identity
meta import SpytialLean.Identity
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
with no instance — the as-written control. -/

public inductive WTree where
  | leaf (n : Nat)
  | node (l r : WTree)
  deriving SpytialIdentity

public inductive UTree where
  | leaf (n : Nat)
  | node (l r : UTree)

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

/-- The runtime classifier of `α`'s instance, for meta-vs-runtime cross-checks. -/
public def rtKey {α : Type} [SpytialIdentity α] (a : α) : Option IdentityKey :=
  (SpytialIdentity.viaOf α).classifier? |>.map (· a)

/-! ## Expr builders (headless, like the TypeShape walker tests) -/

private meta def wleaf (n : Nat) : Expr := mkApp (mkConst ``WTree.leaf) (mkRawNatLit n)
private meta def wnode (l r : Expr) : Expr := mkApp2 (mkConst ``WTree.node) l r
private meta def uleaf (n : Nat) : Expr := mkApp (mkConst ``UTree.leaf) (mkRawNatLit n)
private meta def unode (l r : Expr) : Expr := mkApp2 (mkConst ``UTree.node) l r
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
  let some rkey ← evalKeyOpt (← mkAppM ``rtKey #[val])
    | throwError "{label}: runtime classifier absent"
  unless mkey == rkey do
    throwError "{label}: meta key {repr mkey} ≠ runtime key {repr rkey}"

/-- Differential oracle: the fused walker must agree with the literal two-pass
    reference (fresh atoms, then merge by `(type, identity)`). -/
private meta def assertMatchesReference (label : String) (e : Expr) : MetaM Unit := do
  let (rootF, stF) ← (walkExpr {} e).run {}
  let diF := stF.toDataInstance
  let (rootR, diR) ← referenceRelationalize e
  let cF := canonInstance diF
  let cR := canonInstance diR
  unless cF == cR do
    throwError "{label}: fused ≠ reference\n-- fused --\n{cF}\n-- reference --\n{cR}"
  let idxOf (di : JsonDataInstance) (id : String) : Option Nat :=
    di.atoms.findIdx? (·.id == id)
  unless idxOf diF rootF == idxOf diR rootR do
    throwError "{label}: root atoms disagree"

/-! ## As-written default: no instance ⇒ no merging, literals included -/

#eval show MetaM Unit from do
  let di ← relationalize (unode (uleaf 1) (uleaf 1))
  assertEq "aswritten.labels" (di.atoms.map (·.label)) #["node", "leaf", "1", "leaf", "1"]

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

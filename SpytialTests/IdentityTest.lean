module

public import SpytialLean.Identity
meta import SpytialLean.Identity
-- the deriving handler's generated meta twins reference `MetaEncode`
public meta import SpytialLean.MetaEncode

open SpytialLean Lean Meta

private meta def assert (label : String) (b : Bool) : MetaM Unit := do
  unless b do throwError "{label}: assertion failed"

/-! ## IdentityKey: injective tupling

A composite can never encode the same token as any leaf, and leaves of
different sorts never collide. -/

#guard IdentityKey.ofString "leaf1" != IdentityKey.ofList [.ofString "leaf", .ofNat 1]
#guard IdentityKey.ofNat 1 != IdentityKey.ofString "1"
#guard IdentityKey.ofList [] != IdentityKey.ofString ""
#guard IdentityKey.ofList [.ofString "leaf", .ofNat 1]
         == IdentityKey.ofList [.ofString "leaf", .ofNat 1]

/-! ## ToIdentityKey: encoding without merging

Primitive encodings are pinned exactly where the walker will have to reproduce
them meta-side; lifts are pinned on the injectivity the field rule relies on. -/

open ToIdentityKey (toKey)

#guard toKey (3 : Nat) == IdentityKey.ofNat 3
#guard toKey "leaf" == IdentityKey.ofString "leaf"
#guard toKey true != toKey false
#guard toKey 'a' != toKey 'b'
-- Int keeps its signs apart: `-1` is `negSucc 0`, distinct from `0` and `1`
#guard toKey (1 : Int) != toKey (-1 : Int)
#guard toKey (0 : Int) != toKey (-1 : Int)
#guard toKey (5 : UInt8) != toKey (6 : UInt8)
#guard toKey (5 : USize) != toKey (6 : USize)
-- lifts tag their shape, preserving injective tupling under nesting
#guard toKey ([1, 2] : List Nat) != toKey ([12] : List Nat)
#guard toKey ([] : List (List Nat)) != toKey ([[]] : List (List Nat))
#guard toKey (none : Option (List Nat)) != toKey (some ([] : List Nat))
#guard toKey (#[1, 2] : Array Nat) == toKey (#[1, 2] : Array Nat)
#guard toKey (#[1] : Array Nat) != toKey (#[] : Array Nat)
#guard toKey (([1], [2]) : List Nat × List Nat)
         != toKey (([1, 2], []) : List Nat × List Nat)

/-! ## Derived structural identity -/

inductive ITree where
  | leaf (n : Nat)
  | node (l r : ITree)
  deriving SpytialIdentity

/-- The classifier of `α`'s instance, when it has one. -/
private def keyOf {α : Type} [SpytialIdentity α] (a : α) : Option IdentityKey :=
  (SpytialIdentity.viaOf α).classifier? |>.map (· a)

private def eqvOf {α : Type} [SpytialIdentity α] : α → α → Bool :=
  (SpytialIdentity.viaOf α).toEqv

private def isEqvArm {α : Type u} (s : SpytialIdentity α) : Bool :=
  match s.via with
  | .eqv _ => true
  | .identity _ | .asWritten => false

-- same value, different spelling — one identity
#guard keyOf (ITree.node (.leaf 1) (.leaf 1)) == keyOf (ITree.node (.leaf 1) (.leaf (0 + 1)))
-- different values differ
#guard keyOf (ITree.node (.leaf 1) (.leaf 1)) != keyOf (ITree.node (.leaf 1) (.leaf 2))
#guard keyOf (ITree.leaf 1) != keyOf (ITree.leaf 2)
-- exact key structure: the walker's meta-side computation must reproduce this
-- (the `Nat` field is encoded via `ToIdentityKey`, not merged via an instance)
#guard keyOf (ITree.leaf 1) == some (.ofList [.ofString "leaf", .ofNat 1])
#guard keyOf (ITree.node (.leaf 1) (.leaf 2))
         == some (.ofList [.ofString "node",
                           .ofList [.ofString "leaf", .ofNat 1],
                           .ofList [.ofString "leaf", .ofNat 2]])
-- the derived decider agrees
#guard eqvOf (ITree.node (.leaf 1) (.leaf 1)) (ITree.node (.leaf 1) (.leaf (0 + 1)))
#guard !eqvOf (ITree.leaf 1) (ITree.node (.leaf 1) (.leaf 1))
-- encoded dependencies are total classifiers: no degradation
#guard !isEqvArm (inferInstance : SpytialIdentity ITree)

/-! ## Structures, enums, and proof fields -/

structure Pt where
  x : Nat
  y : Nat
  deriving SpytialIdentity

#guard keyOf (Pt.mk 1 2) == keyOf (Pt.mk 1 2)
#guard keyOf (Pt.mk 1 2) != keyOf (Pt.mk 2 1)

inductive Color where
  | red
  | green
  deriving SpytialIdentity

#guard keyOf Color.red == some (.ofList [.ofString "red"])
#guard keyOf Color.red != keyOf Color.green

-- proof-like fields are erased from identity, matching the walker's
-- `isProofLikeType` field filtering
structure Bounded where
  n : Nat
  ok : n = n
  deriving SpytialIdentity

#guard keyOf (Bounded.mk 3 rfl) == some (.ofList [.ofString "mk", .ofNat 3])

/-! ## Parametric derivation: presentations propagate -/

deriving instance SpytialIdentity for List

-- `List α` requires element *identity*: no `SpytialIdentity Nat`, no
-- `SpytialIdentity (List Nat)` (probed below).
#guard keyOf ([ITree.leaf 1] : List ITree)
         == some (.ofList [.ofString "cons",
                           .ofList [.ofString "leaf", .ofNat 1],
                           .ofList [.ofString "nil"]])
#guard keyOf ([ITree.leaf 1, ITree.leaf 2] : List ITree)
         != keyOf ([ITree.leaf 2, ITree.leaf 1] : List ITree)
-- `keyOf ([] : List ITree) == keyOf ([] : List Color)`: identities are
-- intra-type tokens — the atom table's `(type, identity)` key separates them
-- `List α` is classifier-presented when `α` is …
#guard !isEqvArm (inferInstance : SpytialIdentity (List ITree))

-- … and decider-presented when `α` is: an element type with an `.eqv`
-- presentation (parity) degrades the container to `.eqv`.
structure ModTwo where
  val : Nat

private instance : BEq ModTwo := ⟨fun a b => a.val % 2 == b.val % 2⟩
private instance : SpytialIdentity ModTwo := .ofBEq

#guard isEqvArm (inferInstance : SpytialIdentity ModTwo)
#guard isEqvArm (inferInstance : SpytialIdentity (List ModTwo))
#guard eqvOf [ModTwo.mk 1, ModTwo.mk 2] [ModTwo.mk 3, ModTwo.mk 4]
#guard !eqvOf [ModTwo.mk 1] [ModTwo.mk 2]
#guard !eqvOf [ModTwo.mk 1] [ModTwo.mk 1, ModTwo.mk 3]

/-! ## Encoded fields: the decisive case

A type with a `List Nat` field derives — encoding lifts through `List` — while
`SpytialIdentity (List Nat)` stays unsynthesizable (probed below) even though
the parametric `List` instance above is in scope, so `List Nat` atoms never
merge undeclared. Key composition and atom merging are decoupled. -/

structure Sample where
  xs : List Nat
  deriving SpytialIdentity

#guard keyOf (Sample.mk [1, 2])
         == some (.ofList [.ofString "mk",
                           .ofList [.ofString "list", .ofNat 1, .ofNat 2]])
#guard keyOf (Sample.mk [1, 0 + 1]) == keyOf (Sample.mk [1, 1])
#guard keyOf (Sample.mk [1, 2]) != keyOf (Sample.mk [2, 1])
#guard !isEqvArm (inferInstance : SpytialIdentity Sample)

/-! ## Mixed dependencies: identity for parameters, encoding for the rest

`tag : String` routes through `ToIdentityKey` (no `SpytialIdentity String`
exists); `val : α` routes through the `[SpytialIdentity α]` binder. -/

structure Tagged (α : Type) where
  tag : String
  val : α
  deriving SpytialIdentity

#guard keyOf (Tagged.mk "a" (ITree.leaf 1))
         == some (.ofList [.ofString "mk", .ofString "a",
                           .ofList [.ofString "leaf", .ofNat 1]])
#guard !isEqvArm (inferInstance : SpytialIdentity (Tagged ITree))
-- a decider-presented parameter degrades the whole to `.eqv` …
#guard isEqvArm (inferInstance : SpytialIdentity (Tagged ModTwo))
#guard eqvOf (Tagged.mk "x" (ModTwo.mk 1)) (Tagged.mk "x" (ModTwo.mk 3))
-- … in which the encoded field still discriminates, by key equality
#guard !eqvOf (Tagged.mk "x" (ModTwo.mk 1)) (Tagged.mk "y" (ModTwo.mk 1))

/-! ## Mutual inductives -/

mutual
  inductive EvenL where
    | nilE
    | consE (n : Nat) (t : OddL)
  inductive OddL where
    | consO (n : Nat) (t : EvenL)
end

deriving instance SpytialIdentity for EvenL, OddL

#guard keyOf (EvenL.consE 1 (.consO 2 .nilE)) == keyOf (EvenL.consE 1 (.consO 2 .nilE))
#guard keyOf (EvenL.consE 1 (.consO 2 .nilE)) != keyOf (EvenL.consE 1 (.consO 3 .nilE))

/-! ## ofBEq and ofNorm -/

#guard isEqvArm (SpytialIdentity.ofBEq (α := Nat))

@[reducible] private def modThree : SpytialIdentity Nat := .ofNorm (· % 3) (.identity .ofNat)

#guard modThree.via.classifier?.map (· 4) == modThree.via.classifier?.map (· 1)
#guard modThree.via.classifier?.map (· 1) != modThree.via.classifier?.map (· 2)
#guard modThree.norm?.isSome
-- an `.eqv` base stays decider-presented under `ofNorm`
#guard isEqvArm (SpytialIdentity.ofNorm (· % 3) (.eqv (fun (a b : Nat) => a == b)))

-- `ofNorm n (SpytialIdentity.viaOf T)` on a derived type: identity up to leaf values
private def zeroLeaves : ITree → ITree
  | .leaf _ => .leaf 0
  | .node l r => .node (zeroLeaves l) (zeroLeaves r)

@[reducible] private def shapeOnly : SpytialIdentity ITree :=
  .ofNorm zeroLeaves (SpytialIdentity.viaOf ITree)

#guard shapeOnly.via.classifier?.map (· (ITree.leaf 1))
         == shapeOnly.via.classifier?.map (· (ITree.leaf 2))
#guard shapeOnly.via.classifier?.map (· (ITree.leaf 1))
         != shapeOnly.via.classifier?.map (· (ITree.node (.leaf 1) (.leaf 1)))

/-! ## Instance resolution: the encoding/identity split at search level

`synthInstance?` probes pin the ruled default: primitives encode
(`ToIdentityKey`) but never merge (no `SpytialIdentity`), and the parametric
`List` instance derived above requires element *identity*, so
`SpytialIdentity (List Nat)` fails while `ToIdentityKey (List Nat)` lifts. -/

structure NoInst where
  n : Nat

private meta def hasInst (cls : Name) (ty : Expr) : MetaM Bool := do
  return (← synthInstance? (← mkAppM cls #[ty])).isSome

#eval show MetaM Unit from do
  assert "enc.nat" (← hasInst ``ToIdentityKey (mkConst ``Nat))
  assert "id.nat.not" (!(← hasInst ``SpytialIdentity (mkConst ``Nat)))
  assert "id.string.not" (!(← hasInst ``SpytialIdentity (mkConst ``String)))
  let listNat ← mkAppM ``List #[mkConst ``Nat]
  assert "enc.list-nat" (← hasInst ``ToIdentityKey listNat)
  assert "id.list-nat.not" (!(← hasInst ``SpytialIdentity listNat))
  assert "enc.list-list-nat" (← hasInst ``ToIdentityKey (← mkAppM ``List #[listNat]))
  assert "id.itree" (← hasInst ``SpytialIdentity (mkConst ``ITree))
  assert "id.list-itree" (← hasInst ``SpytialIdentity (← mkAppM ``List #[mkConst ``ITree]))
  -- the parametric binder rule: `Tagged Nat` needs `SpytialIdentity Nat`
  assert "id.tagged-nat.not"
    (!(← hasInst ``SpytialIdentity (← mkAppM ``Tagged #[mkConst ``Nat])))
  assert "id.no-inst.not" (!(← hasInst ``SpytialIdentity (mkConst ``NoInst)))
  assert "enc.no-inst.not" (!(← hasInst ``ToIdentityKey (mkConst ``NoInst)))
  assert "id.list-no-inst.not"
    (!(← hasInst ``SpytialIdentity (← mkAppM ``List #[mkConst ``NoInst])))
  assert "enc.list-no-inst.not"
    (!(← hasInst ``ToIdentityKey (← mkAppM ``List #[mkConst ``NoInst])))

/-! ## Raw and Viewed: instance-search invisibility (the `OrderDual` device)

Both wrappers are semireducible `def`s, so typeclass search — which runs at
reducible transparency — must not see through them: instances on the carrier
must not leak to the wrapper, in either class. Instances declared directly on
the wrapped type must be found. Their mode-shift semantics (quasiquote /
unquote) live in the walker. -/

private instance : SpytialIdentity (Raw Bool) where
  via := .identity fun _ => .ofString "rawBool"

private instance : SpytialIdentity (Viewed Bool) where
  via := .identity fun _ => .ofString "viewedBool"

#eval show MetaM Unit from do
  -- `SpytialIdentity ITree` exists; the wrappers must not inherit it
  assert "raw.invisible" (!(← hasInst ``SpytialIdentity (← mkAppM ``Raw #[mkConst ``ITree])))
  assert "viewed.invisible"
    (!(← hasInst ``SpytialIdentity (← mkAppM ``Viewed #[mkConst ``ITree])))
  -- `ToIdentityKey Nat` exists; same invisibility for the encoding class
  assert "raw.enc-invisible" (!(← hasInst ``ToIdentityKey (← mkAppM ``Raw #[mkConst ``Nat])))
  assert "viewed.enc-invisible"
    (!(← hasInst ``ToIdentityKey (← mkAppM ``Viewed #[mkConst ``Nat])))
  -- instances directly on the wrapper are found, and do not leak back
  assert "raw.direct-instance" (← hasInst ``SpytialIdentity (← mkAppM ``Raw #[mkConst ``Bool]))
  assert "viewed.direct-instance"
    (← hasInst ``SpytialIdentity (← mkAppM ``Viewed #[mkConst ``Bool]))
  assert "raw.no-leak-back" (!(← hasInst ``SpytialIdentity (mkConst ``Bool)))

-- the carrier is defeq underneath (a structure would fail this): the wrappers
-- hide from reducible-transparency instance search only
example : Raw Nat = Nat := rfl
example : Viewed Nat = Nat := rfl

/-! ## Derived-structural registry -/

#eval show MetaM Unit from do
  let env ← getEnv
  assert "ext.itree" (isSpytialStructural env ``ITree)
  assert "ext.pt" (isSpytialStructural env ``Pt)
  assert "ext.color" (isSpytialStructural env ``Color)
  assert "ext.list" (isSpytialStructural env ``List)
  assert "ext.sample" (isSpytialStructural env ``Sample)
  assert "ext.tagged" (isSpytialStructural env ``Tagged)
  assert "ext.evenl" (isSpytialStructural env ``EvenL)
  assert "ext.oddl" (isSpytialStructural env ``OddL)
  -- neither hand-written instances (ModTwo) nor instance-less primitives are
  -- "derived structural"
  assert "ext.nat.not" (!isSpytialStructural env ``Nat)
  assert "ext.string.not" (!isSpytialStructural env ``String)
  assert "ext.modtwo.not" (!isSpytialStructural env ``ModTwo)

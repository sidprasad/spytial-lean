module

public import Lean
public import SpytialLean.Identity
public meta import SpytialLean.Reify

open Lean Meta SpytialLean

/-! ## Bounded generators for the supported constructor fragment -/

private inductive Tree where
  | leaf (value : Nat)
  | node (left right : Tree)
  deriving Repr, DecidableEq, SpytialIdentity

private structure Person where
  name : String
  age : Nat
  deriving Repr, DecidableEq, SpytialIdentity

private def treeToExpr : Tree → Expr
  | .leaf value => mkApp (mkConst ``Tree.leaf) (toExpr value)
  | .node left right => mkApp2 (mkConst ``Tree.node) (treeToExpr left) (treeToExpr right)

private instance : ToExpr Tree where
  toTypeExpr := mkConst ``Tree
  toExpr := treeToExpr

private instance : ToExpr Person where
  toTypeExpr := mkConst ``Person
  toExpr person := mkApp2 (mkConst ``Person.mk) (toExpr person.name) (toExpr person.age)

private def treesUpTo : Nat → Array Tree
  | 0 => #[.leaf 0, .leaf 1]
  | depth + 1 => Id.run do
    let previous := treesUpTo depth
    let mut trees := previous
    for left in previous do
      for right in previous do
        trees := trees.push (.node left right)
    return trees

private def boolListsUpTo : Nat → Array (List Bool)
  | 0 => #[[]]
  | length + 1 => Id.run do
    let previous := boolListsUpTo length
    let mut lists := previous
    for tail in previous do
      lists := lists.push (false :: tail)
      lists := lists.push (true :: tail)
    return lists

/-!
Each sample goes through both relevant paths:

```
value -> reprStr
value -> relationalizeForReify -> rooted datum -> reify expectedType -> reprStr
```

The kernel-checked `rfl` certificate is the primary oracle.  `DecidableEq` and
`Repr` provide independent runtime checks and readable counterexamples; they
are not being used as substitutes for reconstruction.
-/

private meta unsafe def assertRoundTrips {α : Type} [ToExpr α] [DecidableEq α] [Repr α]
    (label : String) (values : Array α) : MetaM Unit := do
  for original in values do
    let certificate ← certifyReifyRoundTrip (toExpr original)
    let reconstructed ← Meta.evalExpr α (toTypeExpr α) certificate.reconstructed
    unless decide (reconstructed = original) do
      throwError "{label}: reconstructed {reprStr reconstructed}, expected {reprStr original}"
    unless reprStr reconstructed == reprStr original do
      throwError "{label}: Repr output changed"

#eval show MetaM Unit from do
  assertRoundTrips "Nat" ((Array.range 33).push 1000)
  assertRoundTrips "String" #["", "plain", "a\"b", "line\nbreak", "λ"]
  assertRoundTrips "Bool" #[false, true]
  assertRoundTrips "Int" #[-8, -3, -1, 0, 1, 3, 8]
  assertRoundTrips "Unit" #[()]
  assertRoundTrips "Option Nat" #[none, some 0, some 1, some 1000]
  assertRoundTrips "List Bool" (boolListsUpTo 4)
  assertRoundTrips "Nat × String" #[(0, ""), (1, "one"), (1, "one")]
  assertRoundTrips "Tree" (treesUpTo 2)
  assertRoundTrips "Person"
    (#[⟨"Ada", 37⟩, ⟨"Grace", 85⟩, ⟨"λ", 0⟩] : Array Person)
  assertRoundTrips "Fin 5" (#[0, 1, 2, 3, 4] : Array (Fin 5))

/-! These primitive wrappers contain omitted decidable proof fields. -/

set_option spytial.identity.auto false in
#eval show MetaM Unit from do
  assertRoundTrips "Char" (#['a', 'λ'] : Array Char)
  assertRoundTrips "UInt8" (#[0, 1, 17, 255] : Array UInt8)

/-! ## Deliberate boundaries -/

private meta def assertFails {α} (label : String) (action : MetaM α) : MetaM Unit := do
  let succeeded ← try
      discard action
      pure true
    catch _ => pure false
  if succeeded then throwError "{label}: unexpectedly succeeded"

private meta def assertFailsWith {α} (label expected : String) (action : MetaM α) : MetaM Unit := do
  try
    discard action
    throwError "{label}: unexpectedly succeeded"
  catch error =>
    let message ← error.toMessageData.toString
    unless message.contains expected do
      throwError "{label}: failed for the wrong reason:\n{message}"

private structure WithFunction where
  apply : Bool → Nat

private instance : SpytialIdentity WithFunction := .asWritten

private structure WithType where
  carrier : Type
  size : Nat

private instance : SpytialIdentity WithType := .asWritten

private structure ModTwo where
  value : Nat

private instance : SpytialIdentity ModTwo :=
  ⟨.eqv (fun left right => left.value % 2 == right.value % 2), none⟩

private structure ModPair where
  left : ModTwo
  right : ModTwo

private structure ViewedPair where
  left : Viewed ModTwo
  right : Viewed ModTwo

private meta def modTwoExpr (value : Nat) : Expr :=
  mkApp (mkConst ``ModTwo.mk) (mkRawNatLit value)

private meta def viewedModTwoExpr (value : Nat) : Expr :=
  mkApp2 (mkConst ``Viewed.mk [0]) (mkConst ``ModTwo) (modTwoExpr value)

private unsafe def unsafeOne : Nat := 1

#eval show MetaM Unit from do
  let hole ← mkFreshExprMVar (some (mkConst ``Nat))
  assertFails "partially instantiated" (certifyReifyRoundTrip hole)

  let argumentType := mkConst ``Bool
  let function := mkLambda `flag .default argumentType (mkRawNatLit 0)
  let withFunction := mkApp (mkConst ``WithFunction.mk) function
  assertFails "function field" (certifyReifyRoundTrip withFunction)

  let withType := mkApp2 (mkConst ``WithType.mk) (mkConst ``Nat) (mkRawNatLit 3)
  assertFails "type field" (certifyReifyRoundTrip withType)

  let modPair := mkApp2 (mkConst ``ModPair.mk) (modTwoExpr 1) (modTwoExpr 3)
  discard <| certifyReifyRoundTrip modPair

  -- `Viewed` changes ordinary visualization walks back to declared identity.
  -- The reification walk must remain occurrence-preserving through the wrapper.
  let viewedPair := mkApp2 (mkConst ``ViewedPair.mk)
    (viewedModTwoExpr 1) (viewedModTwoExpr 3)
  let viewedDatum ← relationalizeForReify viewedPair
  let viewedReconstructed ← reify (mkConst ``ViewedPair) viewedDatum
  unless ← isDefEq viewedPair viewedReconstructed do
    throwError "fidelity mode: Viewed merged structurally unequal fields"

  assertFailsWith "unsafe certificate" "kernel rejected"
    (certifyReifyRoundTrip (mkConst ``unsafeOne))

  let datum ← relationalizeForReify (mkRawNatLit 1)
  let extra := { id := "extra", type := "Nat", label := "2" : JsonAtom }
  let malformedData := { datum.data with atoms := datum.data.atoms.push extra }
  assertFails "unreachable data" (reify (mkConst ``Nat) { datum with data := malformedData })

  let original := toExpr (some 7 : Option Nat)
  let optionDatum ← relationalizeForReify original
  let reorderedData := { optionDatum.data with atoms := optionDatum.data.atoms.reverse }
  let optionNat := mkApp (mkConst ``Option [0]) (mkConst ``Nat)
  let reconstructed ← reify optionNat { optionDatum with data := reorderedData }
  unless ← isDefEq original reconstructed do
    throwError "explicit root: atom reordering changed the reconstructed value"

module

public import SpytialLean
public import Lean.ToExpr
public meta import Lean.Util.CollectAxioms

open Lean Meta SpytialLean

namespace ClosedValueTest

public inductive Tree where
  | leaf (value : Nat)
  | branch (left right : Tree)
  deriving ToExpr, SpytialIdentity, SpytialReify, LosslessIdentity

@[expose] public def sample : Tree := .branch (.leaf 7) (.leaf 7)

-- This succeeds by the universal theorem, not computation of the concrete graph or its decoder.
public theorem sample_roundTrip : reify (relationalize% sample) = Except.ok sample :=
  Structural.reify_relationalize_of_lossless sample

public instance : LosslessIdentity (List Nat) := by spytial_lossless

example : reify (relationalize% ([1, 2, 1] : List Nat)) = Except.ok [1, 2, 1] :=
  Structural.reify_relationalize_of_lossless _

private meta def check (value : Expr) : MetaM Unit := do
  let some result ← ClosedValue.relationalize? value
    | throwError "certified value did not use the typed production route: {value}"
  let (old, provenance, evidence) ← relationalizeRootedWithEvidence value
  unless (toJson old).compress == (toJson result.datum).compress do
    throwError "typed production changed the datum"
  unless provenance.size == result.provenance.size do
    throwError "typed production dropped provenance"
  for (root, term) in provenance.toArray do
    unless (result.provenance[root]?).any (·.equal term) do
      throwError "typed production changed the representative of {root}"
  unless evidence.terms.size == result.evidence.terms.size do
    throwError "typed production dropped selector aliases"
  for (left, right) in evidence.terms.zip result.evidence.terms do
    unless left.1.equal right.1 && left.2 == right.2 do
      throwError "typed production changed selector evidence order"
  let program ← mkAppM ``Structural.relationalizeCandidate #[value]
  unless ← isDefEq result.program program do throwError "not the proved program"
  let expected ← mkAppM ``Structural.reify_relationalize_of_lossless #[value]
  unless ← isDefEq (← inferType result.roundTrip) (← inferType expected) do
    throwError "round-trip proof has the wrong type"
  unless result.roundTrip.getUsedConstants.contains ``Structural.reify_relationalize_of_lossless do
    throwError "production did not reuse the universal theorem"
  checkWithKernel result.roundTrip
  -- Independently check the exact compiled output as well as the pure program's theorem.
  discard <| Reify.certifyReification value result.datum

#eval show MetaM Unit from do
  check (toExpr sample)
  check (mkConst ``sample)
  check (toExpr ([1, 2, 1] : List Nat))
  let leaf := mkApp (mkConst ``Tree.leaf) (mkRawNatLit 7)
  let computed := mkApp (mkConst ``Tree.leaf)
    (mkApp2 (mkConst ``Nat.add) (mkRawNatLit 0) (mkRawNatLit 7))
  check (mkApp2 (mkConst ``Tree.branch) leaf computed)
  let some shared ← ClosedValue.relationalize? (toExpr sample) | throwError "missing route"
  unless shared.datum.data.atoms.size == 3 do throwError "structural sharing was lost"
  for name in #[``sample_roundTrip, ``Structural.reify_relationalize_of_lossless] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected proof dependency: {axioms}"

public inductive Written where
  | leaf (value : Nat)
  | branch (left right : Written)
  deriving ToExpr, SpytialReify

public instance : SpytialIdentity Written := .asWritten
deriving instance LosslessIdentity for Written

#eval show MetaM Unit from do
  let value := toExpr (Written.branch (.leaf 7) (.leaf 7))
  check value
  let some result ← ClosedValue.relationalize? value | throwError "missing asWritten route"
  unless result.datum.data.atoms.size == 4 do throwError "asWritten occurrences were merged"

public structure NoCertificate where
  value : Nat
  deriving ToExpr, SpytialIdentity, SpytialReify

public structure ByEquivalence where
  value : Nat
  deriving ToExpr, SpytialReify

public instance : SpytialIdentity ByEquivalence where
  «via» := .eqv (fun a b => a.value == b.value)

deriving instance LosslessIdentity for ByEquivalence

public meta def customTree : CustomRelationalizer := fun _ _ => do
  let (root, state) := (← get).freshId
  set (state.addAtom { id := root, type := "Tree", label := "custom" })
  return root

#eval show MetaM Unit from do
  let value := toExpr sample
  let raw ← mkAppM ``Raw.mk #[value]
  unless (← ClosedValue.relationalize? raw).isNone do
    throwError "Raw bypassed expression-specific identity semantics"
  unless (← ClosedValue.relationalize? (toExpr (NoCertificate.mk 7))).isNone do
    throwError "used the typed route without a certificate"
  unless (← ClosedValue.relationalize? (toExpr (ByEquivalence.mk 7))).isNone do
    throwError "equivalence identity was treated as occurrence-preserving"
  unless (← ClosedValue.relationalize? value { functionGraphs := true }).isNone do
    throwError "contextual function-graph mode was ignored"
  unless (← ClosedValue.relationalize? value {} #[value]).isNone do
    throwError "observations were ignored"
  let disabled ← withOptions (·.setBool `spytial.identity.auto false) <|
    ClosedValue.relationalize? value
  unless disabled.isNone do throwError "the identity auto flag was ignored"
  let hole ← mkFreshExprMVar (some (mkConst ``Tree))
  unless (← ClosedValue.relationalize? hole).isNone do throwError "accepted an open value"
  withoutModifyingEnv do
    setSpytialRelationalizer ``Tree ``customTree
    unless (← ClosedValue.relationalize? value).isNone do
      throwError "the custom renderer registry was ignored"
    let (datum, _, _) ← Reify.relationalizeWithEvidence value
    unless datum.data.atoms.map (·.label) == #["custom"] do
      throwError "the fallback did not run the custom renderer"

@[irreducible] public def opaqueSample : Tree := .leaf 7

#eval show MetaM Unit from do
  unless (← ClosedValue.relationalize? (mkConst ``opaqueSample)).isNone do
    throwError "the proved route unfolded an opacity boundary"
  let innerRaw ← mkAppM ``Raw.mk #[toExpr (Tree.leaf 7)]
  let nested := mkApp2 (mkConst ``Tree.branch) innerRaw (toExpr (Tree.leaf 7))
  unless (← ClosedValue.relationalize? nested).isNone do
    throwError "a nested Raw wrapper was ignored"
  let raw ← mkAppM ``Raw.mk #[toExpr sample]
  let (old, _, _) ← relationalizeRootedWithEvidence raw
  let (actual, _, _) ← Reify.relationalizeWithEvidence raw
  unless (toJson old).compress == (toJson actual).compress do
    throwError "the fallback changed the occurrence-preserving graph"

section DifferentValueIdentity

local instance (priority := 20000) : ValueIdentity Tree where
  key? _ := none

local instance : LosslessIdentity Tree := by spytial_lossless

#eval show MetaM Unit from withExporting (isExporting := false) do
  unless (← ClosedValue.relationalize? (toExpr sample)).isNone do
    throwError "a ValueIdentity override replaced the production identity policy"

end DifferentValueIdentity

-- The real command takes the typed route; optional certification still checks its concrete output.
set_option spytial.certifyReification true in
#spytial sample

run_cmd Lean.Elab.Command.liftTermElabM do
  let value ← `(sample)
  let .ok operation := Parser.runParserCategory (← getEnv) `spytial_op
      "hideAtom lean (fun n : Nat => n == 7)" | throwError "selector did not parse"
  let props ← spytialPayloadProps value (some #[⟨operation⟩])
  let .str serialized := props.getObjValD "cndSpec" | throwError "missing selector result"
  let .ok spec := Json.parse serialized | throwError "invalid selector JSON"
  let .arr constraints := spec.getObjValD "constraints" | throwError "missing constraints"
  unless (constraints[0]!.getObjValD "hideAtom").getObjValD "selector" == .str "`atom_2" do
    throwError "the production selector did not resolve against the typed datum"

end ClosedValueTest

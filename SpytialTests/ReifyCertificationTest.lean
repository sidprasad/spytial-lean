module

public import SpytialLean
public import Lean.ToExpr
public meta import Lean.Util.CollectAxioms

open Lean Meta SpytialLean

namespace ReifyCertificationTest

#eval show MetaM Unit from do
  for name in #[``Structural.reify_relationalizeAsWritten, ``Structural.reify_relationalize] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "round-trip theorem contains unexpected axioms: {axioms}"

public structure Person where
  name : String
  age : Nat
  deriving ToExpr, SpytialIdentity, SpytialReify

public inductive Tree where
  | leaf (value : Nat)
  | branch (left right : Tree)
  deriving ToExpr, SpytialIdentity, SpytialReify

private meta def checkExactProof (value : Expr) (datum : RootedJsonDataInstance)
    (proof : Expr) : MetaM Unit := do
  let decoded ← mkAppOptM ``reify #[some (← inferType value), none, some (toExpr datum)]
  let expected ← mkEq decoded (← mkAppOptM ``Except.ok
    #[some (mkConst ``ReifyError), some (← inferType value), some value])
  unless ← isDefEq (← inferType proof) expected do
    throwError "certificate is not about the actual datum and original value"
  checkWithKernel proof
  withoutModifyingEnv do
    let name ← mkAuxLemma [] expected proof
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "certificate contains unexpected axioms: {axioms}"

#eval show MetaM Unit from do
  let value := toExpr (⟨"Ada", 37⟩ : Person)
  let raw ← mkAppM ``Raw.mk #[value]
  let (datum, provenance, evidence) ← relationalizeRootedWithEvidence raw
  let proof ← Reify.certifyReification value datum
  checkExactProof value datum proof
  unless proof.getUsedConstants.contains ``reify_of_structurallyRepresents do
    throwError "certification did not use the universal reconstruction theorem"
  unless provenance.size == datum.data.atoms.size && !evidence.terms.isEmpty do
    throwError "production metadata was lost"

#eval show MetaM Unit from do
  let value := toExpr (Tree.branch (.leaf 7) (.leaf 7))
  let (datum, _, _) ← relationalizeRootedWithEvidence value
  unless datum.data.atoms.size == 3 do
    throwError "default structural sharing changed"
  checkExactProof value datum (← Reify.certifyReification value datum)
  -- Relation-array order is not part of the structural interpretation.
  let reordered := { datum with data.relations := datum.data.relations.reverse }
  checkExactProof value reordered (← Reify.certifyReification value reordered)
  -- Changing the emitted graph must invalidate its certificate.
  let altered := { datum with data.atoms := datum.data.atoms.map fun atom =>
    if atom.id == datum.root then { atom with label := "wrongConstructor" } else atom }
  let rejected ← try
    discard <| Reify.certifyReification value altered
    pure false
  catch _ => pure true
  unless rejected do throwError "certified a corrupted graph"

public structure CoarseLeaf where
  value : Nat
  deriving ToExpr, SpytialReify

public instance : SpytialIdentity CoarseLeaf where
  «via» := .identity fun _ => .ofNat 0

public structure Pair where
  left : CoarseLeaf
  right : CoarseLeaf
  deriving ToExpr, SpytialIdentity, SpytialReify

#eval show MetaM Unit from do
  let value := toExpr (⟨⟨1⟩, ⟨2⟩⟩ : Pair)
  let datum ← relationalizeRooted value
  let rejected ← try
    discard <| Reify.certifyReification value datum
    pure false
  catch _ => pure true
  unless rejected do throwError "lossy custom identity was silently accepted"
  unless datum.data.atoms.size == 3 do
    throwError "certification changed the identity policy"
  let raw ← mkAppM ``Raw.mk #[value]
  let written ← relationalizeRooted raw
  checkExactProof value written (← Reify.certifyReification value written)

run_cmd Lean.Elab.Command.liftTermElabM do
  let term ← `(Tree.branch (.leaf 7) (.leaf 7))
  let unchecked ← spytialPayloadProps term
  let checked ← withOptions (fun options =>
    options.setBool spytial.certifyReification.name true) <| spytialPayloadProps term
  unless unchecked == checked do
    throwError "certification changed the widget payload"
  let lossy ← `(Pair.mk (CoarseLeaf.mk 1) (CoarseLeaf.mk 2))
  let rejected ← try
    discard <| withOptions (fun options =>
      options.setBool spytial.certifyReification.name true) <| spytialPayloadProps lossy
    pure false
  catch _ => pure true
  unless rejected do throwError "widget boundary ignored failed certification"

/-- error: spytial reify: certification requires a closed, fully instantiated value -/
#guard_msgs in
set_option spytial.certifyReification true in
#spytial (_ : Nat)

-- Exercise the actual widget command, not a second graph-building test frontend.
set_option spytial.certifyReification true in
#spytial Raw.mk (Person.mk "Ada" 37)

set_option spytial.certifyReification true in
#spytial Tree.branch (.leaf 7) (.leaf 7)

set_option spytial.certifyReification true in
private def checkedDatum : RootedJsonDataInstance := relationalize% (some 7 : Option Nat)

example : reify checkedDatum = Except.ok (some 7 : Option Nat) := by
  apply reify_of_structurallyRepresents
  decide_cbv

end ReifyCertificationTest

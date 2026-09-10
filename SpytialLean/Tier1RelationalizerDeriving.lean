module

public import SpytialLean.Tier1Relationalizer
public meta import SpytialLean.ReifyDeriving
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util

namespace SpytialLean.Tier1Relationalizer.Deriving

open Lean Meta Elab Command Term
open Lean.Elab.Deriving
open Lean.Parser.Term

private meta structure Names where
  describe : Name
  instanceName : Name

private abbrev SimpArg := TSyntax
  [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma]

private meta def mkSimpArg (term : Term) : TermElabM SimpArg :=
  `(Lean.Parser.Tactic.simpLemma| $term:term)

private meta def unsupported (declName : Name) (message : MessageData) : TermElabM α :=
  throwError "cannot derive `Tier1Relationalizer` for `{.ofConstName declName}`: {message}"

private meta def mkNames (plan : SpytialReify.Deriving.Plan) : TermElabM Names := do
  let instanceName ← mkInstName ``Tier1Relationalizer plan.declName
  return { describe := instanceName.appendAfter "_describe", instanceName }

open TSyntax.Compat in
private meta def mkBinders (plan : SpytialReify.Deriving.Plan) :
    TermElabM (Array (TSyntax ``bracketedBinder)) := do
  let mut binders := #[]
  for binder in ← mkImplicitBinders plan.argNames do
    binders := binders.push binder
  for className in #[``SpytialReify, ``Tier1Reification, ``Tier1Identity,
      ``Tier1Relationalizer] do
    for binder in ← mkInstImplicitBinders className plan.indVal plan.argNames do
      binders := binders.push binder
  let indApp ← mkInductiveApp plan.indVal plan.argNames
  binders := binders.push (← `(bracketedBinderF| [Tier1Identity $indApp]))
  return binders

private meta def mkCtorAlternative (plan : SpytialReify.Deriving.Plan) (names : Names)
    (constructor : SpytialReify.Deriving.CtorPlan) : TermElabM (TSyntax ``matchAlt) := do
  let mut patternArguments : Array Term := #[]
  for _ in [:constructor.numParams] do
    patternArguments := patternArguments.push (← `(_))
  let mut fields : Array Ident := #[]
  let mut encodedFields : Array Term := #[]
  for fieldPlan in constructor.fields do
    let field := mkIdent (← mkFreshUserName `field)
    fields := fields.push field
    patternArguments := patternArguments.push field
    let child ← if fieldPlan.recursive then
      `(($(mkIdent names.describe) $field:ident).withIdentity
        (IdentityKey.ofString $(quote plan.declName.toString)) $field:ident)
    else
      `(Tier1Relationalizer.nodeOf $field:ident)
    encodedFields := encodedFields.push
      (← `(Prod.mk $(quote fieldPlan.relation) $child:term))
  let pattern ← `(@$(mkCIdent constructor.name):ident $patternArguments:term*)
  let body ← `({
    typeName := $(quote (shortName plan.declName))
    label := $(quote constructor.label)
    fields := [$encodedFields,*]
  })
  `(matchAltExpr| | $pattern:term => $body:term)

open TSyntax.Compat in
private meta def mkDescribe (plan : SpytialReify.Deriving.Plan) (names : Names) :
    TermElabM (TSyntax `command) := do
  let indApp ← mkInductiveApp plan.indVal plan.argNames
  let binders ← mkBinders plan
  let value := mkIdent (← mkFreshUserName `value)
  let alternatives ← plan.ctors.mapM (mkCtorAlternative plan names)
  let body ← `(match $value:ident with $alternatives:matchAlt*)
  if plan.indVal.isRec then
    `(def $(mkIdent names.describe):ident $binders:bracketedBinder*
        ($value:ident : $indApp) : Tier1Node := $body:term
      termination_by $value:ident)
  else
    `(def $(mkIdent names.describe):ident $binders:bracketedBinder*
      ($value:ident : $indApp) : Tier1Node := $body:term)

private meta def mkFieldComplete (fieldPlan : SpytialReify.Deriving.FieldPlan)
    (datum fuel field inductionHypothesis : Ident) : TermElabM Term := do
  let child := mkIdent (← mkFreshUserName `child)
  let represented := mkIdent (← mkFreshUserName `represented)
  let fieldRepresented := mkIdent (← mkFreshUserName `fieldRepresented)
  let complete ← if fieldPlan.recursive then
    `(fun $child:ident $represented:ident =>
      $inductionHypothesis:ident $child:ident $field:ident $represented:ident)
  else
    `(fun $child:ident $represented:ident =>
      Tier1Relationalizer.representsAt_of_node
        (datum := $datum:ident) (root := $child:ident) (fuel := $fuel:ident)
        (value := $field:ident) $represented:ident)
  `(fun $fieldRepresented:ident =>
    JsonDataInstance.childRepresentsWith_mono $complete:term $fieldRepresented:ident)

private meta partial def mkFieldsComplete
    (constructor : SpytialReify.Deriving.CtorPlan) (fields : Array Ident)
    (datum fuel inductionHypothesis : Ident) (index : Nat := 0) : TermElabM Term := do
  let represented := mkIdent (← mkFreshUserName `represented)
  if h : index < constructor.fields.size then
    let left ← mkFieldComplete constructor.fields[index] datum fuel fields[index]!
      inductionHypothesis
    let right ← mkFieldsComplete constructor fields datum fuel inductionHypothesis (index + 1)
    `(fun $represented:ident =>
      JsonDataInstance.boolAnd_eq_true_mono $left:term $right:term $represented:ident)
  else
    `(fun _ => rfl)

private meta def mkStructuralCompleteAlt
    (constructor : SpytialReify.Deriving.CtorPlan) (describeArg representsArg : SimpArg)
    (datum fuel inductionHypothesis represented : Ident) :
    TermElabM (TSyntax ``Lean.Parser.Tactic.inductionAlt) := do
  let mut fields : Array Ident := #[]
  for _ in constructor.fields do
    fields := fields.push (mkIdent (← mkFreshUserName `field))
  let fieldsComplete ← mkFieldsComplete constructor fields datum fuel inductionHypothesis
  let caseName := mkIdent constructor.name.getString!.toName
  `(Lean.Parser.Tactic.inductionAlt| | $caseName:ident $fields:ident* =>
    simp only [$describeArg, $representsArg, Tier1Node.withIdentity,
      Tier1Structural.Node.representsAt, List.all_cons, List.all_nil]
      at $represented:ident ⊢
    exact JsonDataInstance.constructorRepresents_mono
      $fieldsComplete:term $represented:ident)

open TSyntax.Compat in
private meta def mkInstance (plan : SpytialReify.Deriving.Plan) (names : Names) :
    TermElabM (TSyntax `command) := do
  let indApp ← mkInductiveApp plan.indVal plan.argNames
  let binders ← mkBinders plan
  let value := mkIdent (← mkFreshUserName `value)
  let datum := mkIdent (← mkFreshUserName `datum)
  let root := mkIdent (← mkFreshUserName `root)
  let fuel := mkIdent (← mkFreshUserName `fuel)
  let represented := mkIdent (← mkFreshUserName `represented)
  let inductionHypothesis := mkIdent (← mkFreshUserName `inductionHypothesis)
  let some representsAt :=
      SpytialReify.Deriving.derivedRepresentsName? (← getEnv) plan.declName
    | unsupported plan.declName
        m!"derive `SpytialReify` before `Tier1Relationalizer` in the deriving clause"
  let currentNamespace ← getCurrNamespace
  let describeRef := mkIdentFrom (← getRef) (currentNamespace ++ names.describe)
  let representsRef := mkIdentFrom (← getRef) representsAt
  let describeArg ← mkSimpArg describeRef
  let representsArg ← mkSimpArg representsRef
  let structuralCompleteAlts ← plan.ctors.mapM fun constructor =>
    mkStructuralCompleteAlt constructor describeArg representsArg datum fuel
      inductionHypothesis represented
  let wellFormedProof ← `(by
    induction $value:ident <;>
      simp_all [$describeArg, Tier1Node.withIdentity,
        Tier1Structural.Node.WellFormed, Tier1Structural.Node.FieldsWellFormed,
        Tier1Relationalizer.nodeOf_wellFormed])
  let structuralCompleteProof ← `(by
    change $representsRef:ident $datum:ident $root:ident $fuel:ident $value:ident = true
    induction $fuel:ident generalizing $root:ident $value:ident with
    | zero =>
        simp [$describeArg, $representsArg, Tier1Node.withIdentity,
          Tier1Structural.Node.representsAt] at $represented:ident
    | succ $fuel:ident $inductionHypothesis:ident =>
        cases $value:ident with $structuralCompleteAlts:inductionAlt*)
  `(instance $(mkIdent names.instanceName):ident $binders:bracketedBinder* :
      Tier1Relationalizer $indApp where
    typeKey := IdentityKey.ofString $(quote plan.declName.toString)
    describe := $(mkIdent names.describe)
    wellFormed $value:ident := $wellFormedProof:term
    structuralComplete $datum:ident $root:ident $fuel:ident $value:ident $represented:ident :=
      $structuralCompleteProof:term)

/-- Derive the typed structural frontend and its kernel-checked reconstruction certificate.

This handler accepts the same Tier 1 fragment as `deriving SpytialReify`: regular, first-order,
non-indexed inductive types and structures with explicit data fields and distinct field-relation
names within each constructor. It rejects dependent/indexed families, mutual or nested recursion,
non-regular recursion, and proof-, type-, function-, or implicit-valued data fields.

`SpytialReify` must be derived first, either earlier in the same deriving clause or in an imported
module. The generated description feeds `RelationalizerCore.Engine`; the generated proofs establish
field well-formedness and relate that description to the independent reification checker. -/
public meta def mkTier1RelationalizerHandler (declNames : Array Name) : CommandElabM Bool := do
  unless declNames.size > 0 do return false
  let env ← getEnv
  unless declNames.all fun name => (env.find? name) matches some (.inductInfo _) do return false
  for declName in declNames do
    withoutExposeFromCtors declName do
      let plan ← liftTermElabM <| SpytialReify.Deriving.mkPlan declName
      let names ← liftTermElabM <| mkNames plan
      elabCommand (← liftTermElabM <| mkDescribe plan names)
      elabCommand (← liftTermElabM <| mkInstance plan names)
  return true

meta initialize
  registerDerivingHandler ``Tier1Relationalizer mkTier1RelationalizerHandler

end SpytialLean.Tier1Relationalizer.Deriving

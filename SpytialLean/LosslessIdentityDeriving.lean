module

public import SpytialLean.LosslessIdentity
public meta import SpytialLean.ReifyDeriving
public meta import Lean.Elab.Tactic
import all SpytialLean.Identity
import all SpytialLean.StructuralExposure

namespace SpytialLean.LosslessIdentity.Deriving

open Lean Meta Elab Term Tactic Command
open Lean.Parser.Tactic
open StructuralEncoding

private abbrev SimpArg := TSyntax
  [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma]

private meta structure Member where
  type : Expr
  node : Expr
  key : Expr
  noKey : Bool
  deriving Inhabited

-- This enumerates types, not values. Direct recursion revisits an existing member; no recursion
-- depth or test-value bound is involved in the resulting theorem.
private meta partial def collect (type : Expr) (members : Array Member := #[]) :
    TermElabM (Array Member) := do
  let type ← whnf type
  if members.any (·.type == type) then return members
  if type.hasFVar || type.hasMVar then
    throwError "LosslessIdentity requires a fully instantiated type, not {type}"
  let node ← mkAppOptM ``StructuralExposure.nodeOf #[some type, none, none, none, none]
  let key ← mkAppOptM ``ValueIdentity.key? #[some type, none]
  let noKey ← withLocalDeclD `value type fun value => do
    return (← withTransparency .all <| whnf (mkApp key value)).isAppOf ``Option.none
  let members := members.push { type, node, key, noKey }
  if type.isConstOf ``Nat || type.isConstOf ``String then return members
  let info ← getConstInfoInduct type.getAppFn.constName!
  discard <| SpytialReify.Deriving.mkPlan info.name
  let mut result := members
  for constructor in info.ctors do
    let expression := mkAppN (mkConst constructor type.getAppFn.constLevels!) type.getAppArgs
    result ← forallTelescopeReducing (← inferType expression) fun fields _ => do
      fields.foldlM (fun result field => do collect (← inferType field) result) result
  -- Keep dependencies before their users, including dependencies already encountered through a
  -- sibling. Recursive self-occurrences were marked above, so this is a finite type-level walk.
  return (result.filter (·.type != type)).push members.back!

-- Unfold selected identity definitions, but keep the identity-key algebra abstract. Its proved
-- injectivity lemmas, not reduction of an opaque implementation or native evaluation, do the work.
private meta partial def keyDefinitions (expression : Expr) (seen : NameSet := {}) :
    MetaM NameSet := do
  let mut seen := seen
  for name in expression.getUsedConstants do
    if seen.contains name then continue
    if #[``IdentityKey.ofNat, ``IdentityKey.ofString, ``IdentityKey.ofList,
        ``IdentityKey.ofSpelling].contains name then continue
    let env ← getEnv
    let some (.defnInfo info) := env.find? name | continue
    if let some index := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[index.toNat]!
      if #[`Init, `Lean, `Std].any (·.isPrefixOf origin) then continue
    seen := seen.insert name
    seen ← keyDefinitions info.value seen
  return seen

private meta def simpArgs (names : NameSet) : TermElabM (Array SimpArg) :=
  names.toArray.mapM fun name => do
    `(simpLemma| $(mkCIdent name):ident)

private meta def alternativePattern (count : Nat) (value : Ident) :
    TermElabM (TSyntax ``rcasesPatMed) := do
  let patterns ← (Array.range count).mapM fun _ =>
    `(rcasesPat| ⟨$value:ident, $(mkIdent `rfl):ident⟩)
  `(rcasesPatMed| $patterns:rcasesPat|*)

private meta def memberProof (index count : Nat) (value : Term) : TermElabM Term := do
  let mut proof ← `(Exists.intro $value rfl)
  if index + 1 < count then proof ← `(Or.inl $proof)
  for _ in [:index] do proof ← `(Or.inr $proof)
  return proof

private meta def memberTactic (count : Nat) : TermElabM (TSyntax `tactic) := do
  let mut tactic ← `(tactic| fail "field is outside the collected structural reconstruction family")
  for index in (List.range count).reverse do
    let proof ← memberProof index count (← `(_))
    tactic ← `(tactic| first | exact $proof | $tactic:tactic)
  return tactic

private meta def familyPredicate (members : Array Member) : TermElabM Term := do
  let node := mkIdent (← mkFreshUserName `node)
  let mut predicate ← `(False)
  for index in (List.range members.size).reverse do
    let member := members[index]!
    let type ← exprToSyntax member.type
    let expose ← exprToSyntax member.node
    let entry ← `(∃ value : $type, $node:ident = $expose value)
    predicate ← if index + 1 == members.size then pure entry else `($entry ∨ $predicate)
  `(fun $node:ident => $predicate)

private meta partial def splitFieldMembership (hypothesis : Ident) : TacticM Unit :=
    withMainContext do
  let field ← getFVarId hypothesis
  let type ← whnf (← field.getType)
  if type.isAppOf ``Or then
    evalTactic (← `(tactic| rcases $hypothesis:ident with $hypothesis:ident | $hypothesis:ident))
    let goals ← getGoals
    let mut remaining := []
    for goal in goals do
      setGoals [goal]
      splitFieldMembership hypothesis
      remaining := remaining ++ (← getGoals)
    setGoals remaining
  else
    let rflPat := mkIdent `rfl
    evalTactic (← `(tactic| rcases $hypothesis:ident with ⟨$rflPat:ident, $rflPat:ident⟩))

elab "spytial_split_fields " hypothesis:ident : tactic => splitFieldMembership hypothesis

open TSyntax.Compat in
private meta def deriveProof (type : Expr) : TermElabM Expr :=
    withExporting (isExporting := false) do
  let members ← collect type
  let predicate ← familyPredicate members
  -- Keep the spliced tactic sequence nonempty even when the whole family is unkeyed.
  let mut statements : Array (TSyntax `tactic) := #[← `(tactic| skip)]
  let mut keyLaws : Array SimpArg := #[]
  let mut allDefinitions : NameSet := {}
  for member in members do
    let definitions ← keyDefinitions member.key
    allDefinitions := definitions.toArray.foldl (fun acc name => acc.insert name) allDefinitions
    if member.noKey then continue
    let args := (← simpArgs definitions) ++ keyLaws
    let law := mkIdent (← mkFreshUserName `key_inj)
    let type ← exprToSyntax member.type
    let key ← exprToSyntax member.key
    let x := mkIdent (← mkFreshUserName `x)
    let y := mkIdent (← mkFreshUserName `y)
    -- Class constructors do not have the usual generated `mk.injEq` simp lemma. Congruence
    -- reasoning discharges the remaining constructor equality after simplifying the keys.
    statements := statements.push (← `(tactic|
      have $law:ident : ∀ ($x:ident $y:ident : $type),
          $key $x:ident = $key $y:ident ↔ $x:ident = $y:ident := by
        intro $x:ident $y:ident
        first
        | solve | simp [Int.natCast_inj, $args,*]
        | induction $x:ident generalizing $y:ident <;> cases $y:ident <;>
            (simp_all [Int.natCast_inj, $args,*] <;> grind)))
    keyLaws := keyLaws.push (← `(simpLemma| $law:ident))
  let p := mkIdent (← mkFreshUserName `family)
  let x := mkIdent (← mkFreshUserName `value)
  let y := mkIdent (← mkFreshUserName `other)
  let patternX ← alternativePattern members.size x
  let patternY ← alternativePattern members.size y
  let rootMember ← memberProof (members.size - 1) members.size x
  let witness ← memberTactic members.size
  let allArgs ← simpArgs allDefinitions
  -- Exposure instance bodies are projections; reducing them before constructor case analysis
  -- reveals the generated pattern match without reducing primitive labels.
  let mut exposureNames : NameSet := {}
  for member in members do
    let inst ← synthInstance (← mkAppOptM ``StructuralExposure
      #[some member.type, none, none, none])
    for name in inst.getUsedConstants do
      if (← getEnv).find? name matches some (.defnInfo _) then
        exposureNames := exposureNames.insert name
    let instBody ← withTransparency .all <| whnf inst
    let expose := instBody.getAppArgs[instBody.getAppArgs.size - 3]!
    for name in expose.getUsedConstants do
      if (← getEnv).find? name matches some (.defnInfo _) then
        exposureNames := exposureNames.insert name
  let exposeArgs ← simpArgs exposureNames
  let proof ← `(by
    $statements:tactic*
    let $p:ident := $predicate
    constructor
    intro $x:ident
    apply Node.coherent_of_closed $p:ident (StructuralExposure.nodeOf $x:ident)
    · exact $rootMember
    · intro node member name child field
      change $predicate node at member
      rcases member with $patternX:rcasesPatMed
      all_goals
        cases $x:ident <;>
          (try simp only [StructuralExposure.nodeOf, StructuralExposure.expose,
            ExposedValue.withIdentity, Node.fields, $exposeArgs,*] at field)
        all_goals
          (try simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
            Prod.mk.injEq, false_or, or_false] at field) <;>
              spytial_split_fields field
          all_goals
            change $predicate _
            $witness:tactic
    · intro a b key memberA memberB keyA keyB
      change $predicate a at memberA
      change $predicate b at memberB
      rcases memberA with $patternX:rcasesPatMed
      all_goals
        rcases memberB with $patternY:rcasesPatMed
        all_goals
          have equal := keyA.trans keyB.symm
          first
          | have same : $x:ident = $y:ident := by
              first
              | rfl
              | simpa only [$keyLaws,*] using
                  (StructuralExposure.identity_eq_of_node_key_eq $x:ident $y:ident equal)
            cases same
            rfl
          | solve |
              have types := (StructuralExposure.typeKey_eq_of_node_key $x:ident key keyA).trans
                (StructuralExposure.typeKey_eq_of_node_key $y:ident key keyB).symm
              simp [StructuralExposure.typeKey, natTypeKey, stringTypeKey, $exposeArgs,*] at types
          | simp [StructuralExposure.nodeOf_key, $allArgs,*] at keyA keyB)
  let expected ← mkAppOptM ``LosslessIdentity #[some type, none, none, none, none]
  let result ← withoutErrToSorry <| elabTermEnsuringType proof expected
  synthesizeSyntheticMVarsNoPostponing
  let result ← instantiateMVars result
  if result.hasSorry || result.hasMVar then
    throwError "LosslessIdentity could not construct a complete proof for {type}"
  checkWithKernel result
  return result

/-- Prove losslessness for all values of a supported fully instantiated type, using its selected
identity instances. This constructs an induction proof, not a per-value test or certification. -/
elab "spytial_lossless" : tactic => withMainContext do
  let target ← getMainTarget
  unless target.isAppOf ``LosslessIdentity do
    throwError "spytial_lossless expects a LosslessIdentity goal"
  let type := target.getAppArgs[0]!
  let proof ← deriveProof type
  closeMainGoal `spytial_lossless proof

public meta def mkHandler (declNames : Array Name) : CommandElabM Bool := do
  for name in declNames do
    let info ← getConstInfoInduct name
    unless info.numParams == 0 do
      throwError "derive LosslessIdentity at a concrete instantiation: \
        `instance : LosslessIdentity ({name} ...) := by spytial_lossless`"
    let instanceName ← liftTermElabM <| Lean.Elab.Deriving.mkInstName ``LosslessIdentity name
    elabCommand (← `(@[no_expose] instance $(mkIdent instanceName):ident :
      LosslessIdentity $(mkCIdent name) := by spytial_lossless))
  return true

meta initialize
  registerDerivingHandler ``LosslessIdentity mkHandler

end SpytialLean.LosslessIdentity.Deriving

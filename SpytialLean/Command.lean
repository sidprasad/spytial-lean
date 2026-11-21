module

public import SpytialLean.Enum
public import Lean
public import Lean.Elab.Command
public import Lean.Elab.Term
public import Lean.Elab.Tactic
public import Lean.Widget.UserWidget
public meta import SpytialLean.Types
public meta import SpytialLean.Spec
public meta import SpytialLean.OpElab
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.Reify
public meta import SpytialLean.CounterfactualContext
public meta import SpytialLean.InContext
public meta import SpytialLean.LeanSelector
public meta import SpytialLean.LocalSpec
public meta import SpytialLean.Widget
public meta import SpytialLean.Explorer

namespace SpytialLean

open Lean Elab Command Term Meta Widget

public section

private meta def scopeForType (ty : Expr) : MetaM SelScope := do
  match ← typeHead? ty with
  | some n =>
    let seeds ← ty.getAppArgs.filterMapM fun a => do
      if (← Meta.whnf (← inferType a)) matches .sort _ then typeHead? a else pure none
    SelScope.ofType n seeds
  | none => return { root := `_anonymous, lenient := true }

/-- A term whose type has no head constant gets a fully lenient scope. -/
meta def scopeForExpr (e : Expr) : MetaM SelScope := do
  scopeForType (← inferType e)

/-! ## Widget payload

Whole-value commands and snapshots share `spytialPayloadProps`. Proof and term
inspections also include the evidence retained from their local context. -/

/-- Prefer the current proof's default for the exact type. Global structure defaults
    compose along the parent chain, parent first. -/
private meta def lookupSpecForType (ty : Expr) : MetaM (Option SpytialSpec) := do
  if let some spec ← getProofLayout? ty then return some spec
  let tyHead := (← whnf ty).getAppFn
  match tyHead with
  | .const n _ => do
    let env ← getEnv
    if isStructure env n then
      -- parents come nearest-first; compose root-first, self last
      let parents ← getAllParentStructures n
      let allNames := parents.reverse.toList ++ [n]
      match allNames.filterMap (getSpytialSpec? env ·) with
      | [] => return none
      | specs => return some specs.flatten
    else
      return getSpytialSpec? env n
  | _ => return none

private meta def lookupTypeSpec (e : Expr) : MetaM (Option SpytialSpec) := do
  lookupSpecForType (← inferType e)

private meta def elabTermInstantiated (t : Syntax) : TermElabM Expr := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

private meta structure Observations where
  functions : Array Expr := #[]
  predicates : Array Expr := #[]

/-- Value observers carry an argument template for the walk. Predicate observers
keep the user's partial application so captured arguments never become columns. -/
private meta def resolveObservationTerms (observerSyntaxes : Array Syntax) :
    TermElabM Observations := do
  let mut result : Observations := {}
  for observerSyntax in observerSyntaxes do
    let observer ← elabTermInstantiated observerSyntax
    let (arguments, binderInfos, _) ← forallMetaTelescopeReducing (← inferType observer)
    let explicitArguments := (arguments.zip binderInfos).filterMap fun (argument, info) =>
      if info.isExplicit then some argument else none
    let observation := mkAppN observer arguments
    if ← isProp observation then
      unless (← relationHeadName? observer.getAppFn).isSome do
        throwErrorAt observerSyntax "'observing' expects a named predicate"
      if observer.hasMVar then
        throwErrorAt observerSyntax "fix the predicate's parameters before observing it"
      discard <| classifyLeanRel observer
      unless result.predicates.contains observer do
        result := { result with predicates := result.predicates.push observer }
    else
      unless explicitArguments.size == 1 do
        throwErrorAt observerSyntax m!"'observing' expects a unary function, but \
          '{observerSyntax}' has type {← inferType observer}"
      let resultType ← whnf (← inferType observation)
      if resultType.isSort then
        throwErrorAt observerSyntax "'observing' expects a function returning a data value"
      unless (← graphSide? observation).isSome do
        throwErrorAt observerSyntax "'observing' expects a named function"
      result := { result with functions := result.functions.push observation }
  return result

private meta def resolveObservations (stx : Syntax) : TermElabM Observations :=
  if stx.getNumArgs == 0 then pure {}
  else resolveObservationTerms stx[2].getSepArgs

/-- Elaborate a term to a fully instantiated expression and relationalize it,
    keeping the provenance raw Lean selectors resolve against. -/
private meta def elabRelationalized (t : Syntax) (cfg : WalkConfig := {})
    (observerSyntaxes : Array Syntax := #[]) :
    TermElabM (Expr × Observations × RootedJsonDataInstance × Provenance × SelectorEvidence) := do
  let e ← elabTermInstantiated t
  let observations ← resolveObservationTerms observerSyntaxes
  if observations.predicates.isEmpty then
    let (datum, prov, evidence) ← Reify.relationalizeWithEvidence e cfg observations.functions
    return (e, observations, datum, prov, evidence)
  let (datum, prov, evidence) ← relationalizeRootedWithEvidence e cfg observations.functions
  let (data, evidence) ← observePredicates ⟨e, datum.data, prov, evidence, datum.root⟩
    observations.predicates
  let datum := { datum with data }
  Reify.certifyReificationIfRequested e datum
  return (e, observations, datum, prov, evidence)

private meta def elabOpsWithDefault (type : Expr) (ops : Array (TSyntax `spytial_op))
    (scope? : Option SelScope := none) : TermElabM SpytialSpec := do
  let attached? ← lookupSpecForType type
  if attached?.isNone then
    if let some splice := ops.find? (·.raw.isOfKind ``spytialSpliceStx) then
      logWarningAt splice m!"`..` splices the attached spec, but {type} has none"
  elabSpytialOps (← scope?.getDM (scopeForType type)) ops (some (attached?.getD []))

/-- `scope?` overrides the scope for callers that know more than `e`'s type does. -/
private meta def elabUseSiteOps (e : Expr) (ops : Array (TSyntax `spytial_op))
    (scope? : Option SelScope := none) : TermElabM SpytialSpec := do
  elabOpsWithDefault (← inferType e) ops scope?

/-- Extend a value's ordinary selector scope with explicitly requested
    function graphs. -/
private meta def scopeForObservations (base : SelScope) (observations : Array Expr) :
    MetaM SelScope := do
  let mut relations := #[]
  let mut heads := #[]
  for observation in observations do
    if let some (name, arguments) ← graphSide? observation then
      relations := relations.push (name, arguments.size + 1)
      for argument in arguments.push observation do
        heads := heads.push (← typeHead? (← inferType argument))
  base.withEvidence heads relations

/-- Observation reduction can expose computations absent from the root type
    and the original facts. Their emitted vocabulary is still checked at its
    actual arity, rather than making the whole selector scope lenient. -/
private meta def scopeWithObservedData (scope : SelScope) (data : JsonDataInstance) :
    SelScope := Id.run do
  let mut scope := scope
  for relation in data.relations do
    let arities := if relation.tuples.isEmpty then #[relation.types.size]
      else relation.tuples.map (·.atoms.size)
    for arity in arities do
      scope := scope.addRelation relation.name scope.root (some arity)
  return scope

private meta def elabSpytialPayload (t : Syntax) (ops? : Option (Array (TSyntax `spytial_op)))
    (cfg : WalkConfig) (observerSyntaxes : Array Syntax := #[]) :
    TermElabM (JsonDataInstance × Option String) :=
  -- Both halves derive instances — the walk needs `SpytialIdentity`, the selector
  -- scope needs `SpytialEnum` — so wrapping only the walk would leave the spec
  -- half persisting its own. Both results are plain data.
  withoutModifyingEnv do
    let (e, observations, rooted, prov, evidence) ← elabRelationalized t cfg observerSyntaxes
    let di := rooted.data
    let spec? ← match ops? with
      | some ops => do
        let scope ← scopeForObservations (← scopeForExpr e) observations.functions
        let scope := if observerSyntaxes.isEmpty then scope else scopeWithObservedData scope di
        some <$> elabUseSiteOps e ops (some scope)
      | none => lookupTypeSpec e
    let spec? ← spec?.mapM fun s => liftM (resolveLeanSelectors e di prov s evidence rooted.root)
    return (di, ← spec?.mapM fun s => Lean.ofExcept (SpytialSpec.render s))

private meta def spytialProps (di : JsonDataInstance) (cndSpec? : Option String) : Json :=
  Json.mkObj <|
    [("dataInstance", toJson di)] ++
    match cndSpec? with
    | some s => [("cndSpec", toJson s)]
    -- absent, not null: the widget reads a missing `cndSpec` as free layout
    | none => []

/-- Public so out-of-tree frontends render what the infoview does. -/
public meta def spytialPayloadProps (t : Syntax)
    (ops? : Option (Array (TSyntax `spytial_op)) := none) (cfg : WalkConfig := {})
    (observerSyntaxes : Array Syntax := #[]) :
    TermElabM Json := do
  let (di, cndSpec?) ← elabSpytialPayload t ops? cfg observerSyntaxes
  return spytialProps di cndSpec?

private meta def optionalOps (stx : Syntax) : Option (Array (TSyntax `spytial_op)) :=
  if stx.getNumArgs == 0 then none
  else some (stx[2].getSepArgs.map (⟨·⟩))

private meta def optionalTerms (stx : Syntax) : Array Syntax :=
  if stx.getNumArgs == 0 then #[] else stx[2].getSepArgs

/-- `#spytial <term>` displays a spatial relational diagram in the Lean infoview.
    `observing [f₁, …]` adds function graphs and proved predicate tuples over
    compatible represented values. A `with [<ops>]` list overrides the type's attached
    `spytial_spec`; `..` in the list splices it back in:
    ```
    #spytial myTree with [orientation left left below, atomStyle Tree (borderStyle "#0066ff")]
    #spytial myTree with [.., hideAtom Nat]
    ``` -/
syntax (name := spytialCmd) "#spytial " term (" observing " "[" term,* "]")?
  (" with " "[" spytial_op,*,? "]")? : command

@[command_elab spytialCmd]
meta def elabSpytialCmd : CommandElab := fun stx => do
  let props ← liftTermElabM do
    spytialPayloadProps stx[1] (optionalOps stx[3]) {} (optionalTerms stx[2])
  liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

/-- `spytial_spec <Type> [<ops>]` attaches the spec used by default for that type:
    ```
    spytial_spec Tree [orientation left left below, hideAtom Nat]
    ``` -/
syntax (name := spytialSpecCmd) "spytial_spec " ident " [" spytial_op,*,? "]" : command

@[command_elab spytialSpecCmd]
meta def elabSpytialSpecCmd : CommandElab := fun
  | `(spytial_spec $id:ident [$ops,*]) => do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    liftTermElabM do
      let scope ← SelScope.ofType declName
      let spec ← elabSpytialOps scope ops.getElems
      setSpytialSpec declName spec
  | stx => throwError "Unexpected syntax {stx}."

/-- Set the default layout for inspections of this type in the current goal and its descendants. -/
syntax (name := spytialSpecTactic) "spytial_spec " term:max " [" spytial_op,*,? "]" : tactic

open Tactic in
@[tactic spytialSpecTactic]
meta def elabSpytialSpecTactic : Tactic := fun
  | `(tactic| spytial_spec $root:term [$ops,*]) => withMainContext do
    let type ← instantiateMVars (← Term.withSynthesize <| Term.elabType root)
    if type.hasMVar then throwErrorAt root "a proof-local layout requires a fully specified type"
    let spec ← elabOpsWithDefault type ops.getElems
    replaceMainGoal [← attachProofLayout (← getMainGoal) type spec]
  | _ => throwUnsupportedSyntax

/-- `spytial_ops <name> : <Type> [<ops>]` binds a reusable op list, elaborated
    against `<Type>` as root. The name is declared as an `SpytialOps` constant,
    so it namespaces and is reached through `open` and `export` like any other.
    ```
    spytial_ops quiet : Tree [hideAtom Nat]
    #spytial t with [..quiet, orientation left below]
    ``` -/
syntax (name := spytialOpsCmd) "spytial_ops " ident " : " ident " [" spytial_op,*,? "]" : command

@[command_elab spytialOpsCmd]
meta def elabSpytialOpsCmd : CommandElab := fun
  | `(spytial_ops $name:ident : $ty:ident [$ops,*]) => do
    let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo ty
    -- a `module` file makes declarations private by default, and a list nobody
    -- downstream can splice is useless; the syntax has no visibility modifier
    let (declName, _) ← mkDeclName (← getCurrNamespace) { visibility := .public } name.getId
    let spec ← liftTermElabM do
      let scope ← SelScope.ofType root
      elabSpytialOps scope ops.getElems
    let declId := mkIdentFrom name (`_root_ ++ declName)
    elabCommand (← `(public meta def $declId : SpytialOps := .mk))
    liftCoreM <| setSpytialOps declName { root, ops := spec }
  | stx => throwError "Unexpected syntax {stx}."

/-! ## spytial_relationalizer command -/

/-- `spytial_relationalizer <TypeName> <defName>` registers a custom relationalizer
    for a type. The def must have type `CustomRelationalizer`, and — to be usable
    from importing modules — should be `public meta def`.

    ```
    public meta def myRelationalizer : CustomRelationalizer := fun e walkExpr => do ...

    spytial_relationalizer MyType myRelationalizer
    ```
-/
syntax (name := spytialRelationalizerCmd) "spytial_relationalizer " ident ident : command

@[command_elab spytialRelationalizerCmd]
meta def elabSpytialRelationalizerCmd : CommandElab := fun
  | `(spytial_relationalizer $typeId:ident $defId:ident) => do
    let typeName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo typeId
    let defName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo defId
    -- fail mistyped registrations here, not opaquely at dispatch
    liftTermElabM do
      let declType := (← getConstInfo defName).type
      unless (← Meta.isDefEq declType (Lean.mkConst ``CustomRelationalizer)) do
        throwError s!"'{defName}' must have type `CustomRelationalizer`"
    if isPrivateName defName then
      logWarningAt defId m!"'{defName}' is not `public`, so a `#spytial` on this \
        type from an importing module fails at render with `Unknown constant` — \
        declare it `public meta def`"
    liftCoreM <| setSpytialRelationalizer typeName defName
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Debugging commands -/

/-- `#spytial.spec <term> with [<ops>]` prints the spec string handed to
    spytial-core. Useful for debugging whether the spec is what you expect. -/
syntax (name := spytialSpecDebug) "#spytial.spec " term " with " "[" spytial_op,*,? "]" : command

@[command_elab spytialSpecDebug]
meta def elabSpytialSpecDebug : CommandElab := fun
  | `(#spytial.spec $t:term with [$ops,*]) => do
    let specStr ← liftTermElabM do
      let e ← elabTermInstantiated t
      let spec ← elabUseSiteOps e ops.getElems
      -- Plain relational selectors can lower without walking the term.
      if spec.needsDatum then
        let (rooted, prov, evidence) ← Reify.relationalizeWithEvidence e
        Lean.ofExcept (← resolveLeanSelectors e rooted.data prov spec evidence rooted.root).render
      else
        Lean.ofExcept spec.render
    logInfo m!"{specStr}"
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.datum <term>` prints the generated JSON data instance; it accepts
    the same `observing` clause as `#spytial`. -/
syntax (name := spytialDatumDebug) "#spytial.datum " term
  (" observing " "[" term,* "]")? : command

@[command_elab spytialDatumDebug]
meta def elabSpytialDatumDebug : CommandElab := fun stx => do
  let (_, _, di, _, _) ← liftTermElabM do
    elabRelationalized stx[1] {} (optionalTerms stx[2])
  logInfo m!"{(toJson di.data).pretty}"

/-- `#spytial.proof <term>` draws a proof term without filtering Prop-typed fields. -/
syntax (name := spytialProofCmd) "#spytial.proof " term (" with " "[" spytial_op,*,? "]")? : command

@[command_elab spytialProofCmd]
meta def elabSpytialProofCmd : CommandElab := fun
  | stx@`(#spytial.proof $t:term) => do
    let props ← liftTermElabM <| spytialPayloadProps t none { filterProofs := false }
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx@`(#spytial.proof $t:term with [$ops,*]) => do
    let props ← liftTermElabM <|
      spytialPayloadProps t (some ops.getElems) { filterProofs := false }
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx
  | stx => throwError "Unexpected syntax {stx}."

/-- `#spytial.proof.datum <term>` prints the proof-mode data instance as JSON. -/
syntax (name := spytialProofDatumDebug) "#spytial.proof.datum " term : command

@[command_elab spytialProofDatumDebug]
meta def elabSpytialProofDatumDebug : CommandElab := fun
  | `(#spytial.proof.datum $t:term) => do
    let (_, _, di, _, _) ← liftTermElabM <| elabRelationalized t { filterProofs := false }
    logInfo m!"{(toJson di.data).pretty}"
  | stx => throwError "Unexpected syntax {stx}."

declare_syntax_cat spytialEvidenceClause
syntax "fyi " "[" term,* "]" : spytialEvidenceClause
syntax "nvm " "[" ident,* "]" : spytialEvidenceClause

/-- Spytial's context preparation configuration. Simp is always enabled: it
    normalizes each fact before decomposition, so a constructor clash reduces
    to `False` (an inconsistent context) and a same-constructor equation
    splits into the field equalities that refine atoms. -/
private meta def contextConfig : InspectionConfig := { simplify := true }

private meta def resolveContextConfig (clauses : Syntax) : TermElabM InspectionConfig := do
  let mut config : InspectionConfig := contextConfig
  for clause in clauses.getArgs do
    match clause with
    | `(spytialEvidenceClause| fyi [$rules:term,*]) =>
      for rule in rules.getElems do
        -- Keep a bare local's identity, including rules with implicit binders.
        let e ← if rule.raw.isIdent then
          match ← Term.resolveId? rule (withInfo := true) with
          | some e@(.fvar _) => pure e
          | _ => elabTermInstantiated rule
        else elabTermInstantiated rule
        unless ← isProp (← inferType e) do
          throwErrorAt rule m!"'fyi' expects a hypothesis: a proof of a Prop-typed \
            statement, but this term has type {← inferType e}"
        config := { config with hypotheses := config.hypotheses.push e }
    | `(spytialEvidenceClause| nvm [$names:ident,*]) =>
      for name in names.getElems do
        let some (.fvar id) ← Term.resolveId? name (withInfo := true)
          | throwErrorAt name "'nvm' expects the name of a local declaration"
        config := { config with excludedHypotheses := config.excludedHypotheses.push id }
    | _ => throwUnsupportedSyntax
  return config

private meta structure InspectionPayload where
  props : Json
  propositions : Array Expr

/-- Prepare and inspect the local context, then build the widget payload. -/
private meta def preparedContextProps? (subject : Expr) (prepared : InspectionContext)
    (ops? : Option (Array (TSyntax `spytial_op)) := none)
    (walkConfig : WalkConfig := {}) (config : InspectionConfig := contextConfig)
    (observations predicates : Array Expr := #[]) :
    TermElabM (Option InspectionPayload × ContextViewStatus) := do
  let (status, view?) ← inspectPreparedContext subject prepared walkConfig config observations predicates
  let some view := view? | return (none, status)
  let spec? ← match ops? with
    | some ops => do
      let scope ← scopeForContext view.context (← scopeForExpr subject) observations
      let scope := if observations.isEmpty && predicates.isEmpty then scope
        else scopeWithObservedData scope view.data
      some <$> elabUseSiteOps subject ops (some scope)
    | none => lookupTypeSpec subject
  -- Both selector styles range over this datum. Lean predicates retain the
  -- represented terms and checked evidence instead of reading display labels.
  let spec? ← spec?.mapM fun s =>
    liftM (resolveLeanSelectors view.datum view.data view.prov s view.evidence view.inspection.root)
  let props := spytialProps view.data
    (← spec?.mapM fun s => Lean.ofExcept (SpytialSpec.render s))
  -- Only exact Lean free-variable identities establish cross-view correspondence.
  -- Atom IDs and pretty names are local to one walk and cannot establish it.
  let identities := view.evidence.terms.filterMap fun (term, atom) =>
    match term with
    | .fvar id => some (Json.mkObj [
        ("atom", toJson atom), ("identity", toJson id.name.toString)])
    | _ => none
  let mut context := #[]
  let mut hypotheses : Std.HashMap FVarId Nat := {}
  for localDecl in ← getLCtx do
    if localDecl.isImplementationDetail then continue
    if !config.excludedHypotheses.contains localDecl.fvarId && (← isProp localDecl.type) then
      hypotheses := hypotheses.insert localDecl.fvarId context.size
    let type ← ppExpr localDecl.type
    let value ← localDecl.value?.mapM fun e => return (← ppExpr e).pretty
    let entry := Json.mkObj [
      ("name", toJson localDecl.userName.toString), ("type", toJson type.pretty),
      ("value", toJson value)]
    context := context.push (if config.excludedHypotheses.contains localDecl.fvarId then
      entry.setObjVal! "excluded" (toJson true) else entry)
  -- Keep references to the actual local entries, including for projections and
  -- proofs that use several hypotheses. Display names can be shadowed.
  let sources := view.context.proofs.map fun proof =>
    ((collectFVars {} proof).fvarIds.filterMap (fun id => hypotheses[id]?)).qsort (· < ·)
  let props := props.setObjVal! "inspection" (toJson view.inspection)
    |>.setObjVal! "factSources" (toJson sources)
    |>.setObjVal! "identities" (toJson identities)
    |>.setObjVal! "localContext" (toJson context)
    |>.setObjVal! "observations" (toJson ((← observations.mapM fun e =>
        return (← ppExpr e.getAppFn).pretty) ++ (← predicates.mapM fun p => liftM (predicateObservationName p))))
  let propositions ← withLCtx view.context.scope view.context.localInstances do
    view.context.proofs.mapM fun proof => do instantiateMVars (← inferType proof)
  return (some { props, propositions }, status)

/-- Programmatic entry point for inspecting a term in its current local context. -/
public meta def spytialInContextProps (subject : Expr)
    (ops? : Option (Array (TSyntax `spytial_op)) := none)
    (walkConfig : WalkConfig := {}) (hypotheses : Array Expr := #[])
    (observations predicates : Array Expr := #[]) :
    TermElabM (Json × ContextViewStatus) := do
  let config := { contextConfig with hypotheses }
  let (payload?, status) ← preparedContextProps? subject (← prepareInspectionContext subject config)
    ops? walkConfig config observations predicates
  let some payload := payload? | throwError "spytial: inconsistent context"
  return (payload.props, status)

/-- Print the original inspection with one additional evidence clause, keeping its
    observations, layout, title, explicit rules and previous omissions. -/
private meta def omissionCommand (stx : Syntax) (omitted : Array FVarId) : TermElabM String := do
  let names ← omitted.mapM fun id => return mkIdent (← id.getUserName)
  let clause ← `(spytialEvidenceClause| nvm [$names:ident,*])
  if let .original .. := stx[0].getHeadInfo then
    if let some range := stx.getRange? true then
      if let some cut := (#[stx[3], stx[2], stx[1]].findSome? (·.getTailPos? true)) then
        let source := (← getFileMap).source
        let before := (Substring.Raw.mk source range.start cut).toString
        let after := (Substring.Raw.mk source cut range.stop).toString
        let extra := (← PrettyPrinter.ppCategory `spytialEvidenceClause clause).pretty
        return s!"{before} {extra}{after}"
  let site := stx.setArg 3 (mkNullNode (stx[3].getArgs.push clause.raw))
  return (← PrettyPrinter.ppCategory `tactic (mkNode `SpytialLean.spytialTactic #[site])).pretty

private meta def contradictionPayload (subject : Expr) (stx : Syntax) (report : ContradictionReport)
    (observations predicates : Array Expr) : TermElabM InspectionPayload := do
  let conflicts ← report.conflicts.mapM fun ids => ids.mapM fun id => do
    return s!"{← ppExpr (mkFVar id)} : {← ppExpr (← id.getType)}"
  let mut previews := #[]
  for preview in report.previews do
    let command ← omissionCommand stx preview.omitted
    let omitted ← preview.omitted.mapM fun id => return (← id.getUserName).toString
    -- A layout may refer to a relation that disappears when its evidence is omitted.
    -- Keep a failed replay local to that command; other previews may still render.
    let entry ← try
      let (some payload, status) ← preparedContextProps? subject preview.context
        (optionalOps stx[4]) {} preview.config observations predicates | unreachable!
      pure <| Json.mkObj [("command", toJson command), ("view", payload.props),
        ("truncated", toJson status.truncated)]
    catch ex =>
      let .error _ message := ex | throw ex
      pure <| Json.mkObj [("command", toJson command), ("error", toJson (← message.toString))]
    previews := previews.push (entry.setObjVal! "omitted" (toJson omitted))
  let diagnosis := Json.mkObj [("term", toJson (← ppExpr subject).pretty),
    ("conflicts", toJson conflicts), ("previews", Json.arr previews), ("limited", toJson report.limited)]
  return { props := Json.mkObj [("diagnosis", diagnosis)], propositions := #[] }

private meta def inspectionPointProps (subject : Expr) (stx : Syntax) :
    TermElabM (Option InspectionPayload) := do
  let observers ← resolveObservations stx[2]
  let config ← resolveContextConfig stx[3]
  let prepared ← prepareInspectionContext subject config
  if let some proof := prepared.contradiction? then
    let report ← inspectCounterfactuals subject config proof
    let payload ← contradictionPayload subject stx report observers.functions observers.predicates
    logWarning "spytial: inconsistent context; see the inspection for conflicts and counterfactuals"
    return some payload
  let (props?, status) ← preparedContextProps? subject prepared (optionalOps stx[4]) {}
    config observers.functions observers.predicates
  if status.truncated then
    logWarning "spytial: context preparation reached a limit; the diagram may be incomplete"
  return props?

private meta def saveInspectionPoint (invocation : Syntax) (payload : InspectionPayload)
    (scope : String) (branch : Name := .anonymous) : CoreM Unit := do
  let fileMap ← getFileMap
  let line := invocation.getPos?.map fun p => (fileMap.toPosition p).line
  let caption? := invocation[5][1].isStrLit?
  let props := if let some ids := (← inspectionFactIds? payload.propositions) then
    payload.props.setObjVal! "factIds" (toJson ids) else payload.props
  let props := props.setObjVal! "point" (Json.mkObj [
    ("title", toJson caption?), ("line", toJson line),
    ("scope", toJson scope), ("branch", toJson (if branch.isAnonymous then "" else branch.toString))])
  recordInspection invocation props
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) invocation

syntax spytialSite := "spytial " term (" observing " "[" term,* "]")?
  spytialEvidenceClause* (" with " "[" spytial_op,*,? "]")? (" titled " str)?

open Tactic in
/-- `spytial term` inspects a term using its computed structure and local proof evidence,
    translates supported propositions into relational data, and displays it.
    `observing [f₁, ...]` displays function graphs and proved predicate tuples.
    `fyi [h₁, ...]` supplies proofs or forward rules for Aesop;
    `nvm [h₁, ...]` omits local declarations from this extraction;
    `with [...]` supplies Spytial layout operations. -/
syntax (name := spytialTactic) spytialSite : tactic

open Tactic in
@[tactic spytialTactic]
meta def elabSpytialTactic : Tactic := fun stx => withMainContext do
  let stx := stx[0]
  let goal ← getMainGoal
  let some props ← inspectionPointProps (← elabTermInstantiated stx[1]) stx | return
  saveInspectionPoint stx props goal.name.toString (← goal.getTag)

/-- Inspect an expression in the surrounding local context and return the expression itself.
    The optional clauses have the same meanings as in the `spytial` tactic. -/
macro (name := spytialTerm) site:spytialSite : term => do
  -- As in Lean's `show_term`, leave implicit lambda insertion to the inspected expression.
  let inner : Term := ⟨site.raw⟩
  `(no_implicit_lambda% $inner)

private meta def inspectTermValue (stx : Syntax) (value : Expr) : TermElabM Unit := withRef stx do
  -- Inspection may do proof search and synthesize instances. Keep its assignments out of
  -- the enclosing function, whose remaining constraints Lean may still be solving.
  let props? ← try
    withoutModifyingStateWithInfoAndMessages <| withoutErrToSorry do
      inspectionPointProps value stx
  catch ex =>
    let .error _ message := ex | throw ex
    logWarningAt stx m!"spytial: could not inspect this expression: {message}"
    pure none
  if let some props := props? then
    saveInspectionPoint stx props (← termInspectionScope stx)

/-- A free variable contains only its ID. Its inferred type and the declarations captured
    by the widget can still contain metavariables after the expression itself is known. -/
private meta def tryInspectTerm (stx : Syntax) (value : Expr) : TermElabM Bool := do
  let subject ← instantiateMVars value
  if subject.hasMVar || (← instantiateMVars (← inferType subject)).hasMVar then return false
  for decl in ← getLCtx do
    let decl ← instantiateLocalDeclMVars decl
    if decl.type.hasMVar || (decl.value? (allowNondep := true)).any (·.hasMVar) then return false
  inspectTermValue stx subject
  return true

@[term_elab spytialSite]
meta def elabSpytialTerm : TermElab := fun stx expectedType? => do
  let value ← withSynthesizeLight <| elabTermEnsuringType stx[1] expectedType?
  unless ← tryInspectTerm stx value do
    let unitType := Lean.mkConst ``Unit
    let unitValue := Lean.mkConst ``Unit.unit
    -- On the last ordinary retry Lean can still default numerals or run queued tactics
    -- (e.g. a later `by rfl` that fixes a let value). Queue the final check behind those.
    let finalCheck : FixedTermElab := fun _ => do
      unless ← tryInspectTerm stx value do
        logWarningAt stx "spytial: unresolved expression or local context; no diagram rendered"
      return unitValue
    elabToSyntax (fun _ => do
      if ← tryInspectTerm stx value then return unitValue
      tryPostpone
      elabToSyntax finalCheck fun check => withRef .missing do
        elabTerm (← `(by exact $check)) (some unitType)) fun pending =>
          discard <| postponeElabTerm pending (some unitType)
  return value

meta def spytialDatumKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.datum" (includeIdent := true)

open Tactic in
/-- `spytial.datum term` prints the relational data produced by context inspection.
    It accepts the same observations and optional hypotheses as `spytial`. -/
syntax (name := spytialDatumTactic) spytialDatumKw term
  (" observing " "[" term,* "]")?
  spytialEvidenceClause* : tactic

open Tactic in
@[tactic spytialDatumTactic]
meta def elabSpytialDatumTactic : Tactic := fun stx => withMainContext do
  let subject ← elabTermInstantiated stx[1]
  let observations ← resolveObservations stx[2]
  let (status, view?) ← inspectInContext subject {}
    (← resolveContextConfig stx[3]) observations.functions observations.predicates
  if status.inconsistent then
    logWarning "spytial: inconsistent context; no datum produced"
  else if let some view := view? then
    logInfo m!"{(toJson view.data).pretty}"
    if status.truncated then
      logWarning "spytial: context preparation reached a limit; the datum may be incomplete"


/-- A dotted atom never enters the token table — the lexer reads `spytial.proof`
    as one qualified identifier — so an atom-led rule can never fire. Without
    `includeIdent` the rule is not indexed under ident and is never tried. -/
meta def spytialProofKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.proof" (includeIdent := true)

open Tactic in
/-- `spytial.proof <term>` is `#spytial.proof` in tactic mode. -/
syntax (name := spytialProofTactic) spytialProofKw term
  (" with " "[" spytial_op,*,? "]")? : tactic

open Tactic in
@[tactic spytialProofTactic]
meta def elabSpytialProofTactic : Tactic := fun stx => do
  -- a quotation pattern would lex `spytial.proof` as one dotted ident and never match
  let props ← withMainContext do
    spytialPayloadProps stx[1] (optionalOps stx[2]) { filterProofs := false }
  savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

end

end SpytialLean

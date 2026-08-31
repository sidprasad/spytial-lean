module

public meta import Iykyk.Extract
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.SelectorElab

namespace SpytialLean

open Lean Meta

public section

/-!
# Relationalizing IYKYK knowledge

IYKYK extracts proof-backed knowledge about a selected term. This module is a
Spytial consumer: it translates that knowledge into the atoms and relations
accepted by Spytial's existing rendering pipeline. Proof checking, bounded
inference, witness scope, and inconsistency belong to IYKYK.
-/

private meta def isNegation (proposition : Expr) : Bool :=
  match proposition with
  | .app (.const ``Not _) _ => true
  | .forallE _ _ body _ => !body.hasLooseBVar 0 && body.isConstOf ``False
  | _ => false

/-- The positive relation represented by a known proposition. Equations with a
    named application become function-graph tuples. Negative and disjunctive
    knowledge does not produce an unconditional tuple. -/
public meta def propTupleShape? (proposition : Expr) : MetaM (Option (String × Array Expr)) := do
  unless ← isProp proposition do return none
  if proposition.isAppOfArity ``Or 2 then return none
  if let some (_, domain, result) := proposition.eq? then
    if let some (name, args) ← graphSide? domain then
      return some (name, args.push result)
    if let some (name, args) ← graphSide? result then
      return some (name, args.push domain)
  if isNegation proposition then return none
  let some name ← propRelName? proposition.getAppFn | return none
  let args ← dataArgsOf proposition
  if args.isEmpty then return none
  return some (name, args)

/-- An equality that supplies visible structure for a local variable. An
    equation involving a named application remains a relation instead. -/
private meta def refinementOf? (proposition : Expr) : MetaM (Option (FVarId × Expr)) := do
  let some (_, lhs, rhs) := proposition.eq? | return none
  let pick (id : FVarId) (other : Expr) : MetaM (Option (FVarId × Expr)) := do
    if other.containsFVar id then return none
    if (← graphSide? other).isSome then return none
    return some (id, other)
  match lhs, rhs with
  | .fvar id, _ => pick id rhs
  | _, .fvar id => pick id lhs
  | _, _ => return none

/-- Local definitions determine a variable even when no proposition states an
    equality. -/
private meta def definitionalRefinements : MetaM (Array (FVarId × Expr)) := do
  let mut refinements := #[]
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    if let some value := declaration.value? then
      let value ← instantiateMVars value
      unless value.containsFVar declaration.fvarId do
        refinements := refinements.push (declaration.fvarId, value)
  return refinements

/-- Substitute known variable refinements through a compound relation
    endpoint, allowing projections such as `t.left` to reach the atom already
    used for the corresponding constructor field. -/
private meta partial def reduceKnown (refinements : Std.HashMap FVarId Expr)
    (fuel : Nat) (expression : Expr) (observations : Array Expr := #[]) : MetaM Expr := do
  let replaced := expression.replace fun subexpression =>
    match subexpression with
    | .fvar id => refinements[id]?
    | _ => none
  if replaced.equal expression then return expression
  if fuel == 0 then return replaced
  let reduced ← if (← observedGraphSide? { observations } replaced).isSome then
    pure replaced else whnf replaced
  if reduced.isFVar || reduced.isMVar then return reduced
  reduceKnown refinements (fuel - 1) reduced observations

/-- Substitute known local values without reducing the surrounding program,
    retaining a Lean expression for selectors and contextual relevance. -/
private meta partial def substituteKnown (refinements : Std.HashMap FVarId Expr)
    (fuel : Nat) (expression : Expr) : Expr :=
  let replaced := expression.replace fun subexpression =>
    match subexpression with
    | .fvar id => refinements[id]?
    | _ => none
  if replaced.equal expression || fuel == 0 then replaced
  else substituteKnown refinements (fuel - 1) replaced

private meta def contextArgument (cfg : WalkConfig) (argument : Expr) :
    MetaM Expr :=
  if argument.isFVar || argument.isMVar then pure argument
  else reduceKnown cfg.refinements 8 argument cfg.observations

/-- Recover the proposition in the vocabulary in which its proof was built.
    IYKYK normalizes propositions for matching; a consumer should still call
    `x < y` by its source relation `lt`, rather than exposing its reduction to
    `Nat.le (Nat.succ x) y`. -/
private meta def displayedProposition (fact : Iykyk.KnownFact) : MetaM Expr :=
  do instantiateMVars (← inferType fact.proof)

/-- Allocate the shared unknowns before anything else walks. Registering each
    choice term in `applicationAtoms` makes all of its occurrences reuse the
    same short-labelled atom rather than displaying `Classical.choose`, and the
    labels come from the walk's one `•ₙ` counter so no other generated atom can
    repeat them. -/
private meta def addWitnesses (afaik : Iykyk.Afaik) (recordObservationTerms : Bool) :
    StateT WalkState MetaM (Array (Expr × String)) := do
  let mut anchors := #[]
  for witness in afaik.witnesses do
    -- The walk reduces before its `applicationAtoms` lookup, so an occurrence
    -- inside the root is found under the reduced spelling.
    let reduced ← whnf witness.term
    let state ← get
    let (label, state) := state.freshApplicationLabel
    let (atomId, state) := state.freshId
    let atom : JsonAtom := {
      id := atomId
      type := ← sigOfType witness.type
      label
    }
    set { state.addAtom atom with
      applicationAtoms :=
        (state.applicationAtoms.insert ⟨witness.term⟩ atomId).insert ⟨reduced⟩ atomId
      observationTerms := if recordObservationTerms then
        state.observationTerms.push (witness.term, atomId)
      else state.observationTerms }
    anchors := anchors.push (witness.term, atomId)
  return anchors

/-- Emit one known proposition while reusing atoms already allocated for the
    root, shared witnesses, and repeated relation endpoints. -/
private meta def walkFact (cfg : WalkConfig)
    (fact : Iykyk.KnownFact) (initialAnchors : Array (Expr × String)) :
    StateT WalkState MetaM (Array (Expr × String)) := do
  let some (relation, rawArguments) ← propTupleShape? (← displayedProposition fact)
    | return initialAnchors
  -- Predicates that differ only past their short name land in one relation; a
  -- tuple of another width would corrupt it, so the colliding fact stays
  -- undrawn instead.
  if let some (declaredTypes, _) := (← get).relations.get? relation then
    if declaredTypes.size != rawArguments.size then
      logWarning m!"spytial: '{relation}' names relations of arity \
        {declaredTypes.size} and {rawArguments.size}; the second is not drawn"
      return initialAnchors
  let mut anchors := initialAnchors
  let mut atomIds := #[]
  let mut types := #[]
  for rawArgument in rawArguments do
    let argument ← contextArgument cfg rawArgument
    let mut atomId? := none
    for (seen, atomId) in anchors do
      if seen.equal argument then
        atomId? := some atomId
        break
    let atomId ← match atomId? with
      | some atomId => pure atomId
      | none => do
        let atomId ← walkExpr cfg argument
        anchors := anchors.push (argument, atomId)
        pure atomId
    atomIds := atomIds.push atomId
    types := types.push (← sigOfType (← inferType argument))
  -- An observation may already have emitted the graph point established by
  -- this equation. Relations contain tuples, not one copy per justification.
  unless ((← get).relations.get? relation).any (fun (_, tuples) =>
      tuples.any (·.atoms == atomIds)) do
    modify fun state => state.addTuple relation types { atoms := atomIds, types }
  return anchors

private meta def contextWalkConfig (afaik : Iykyk.Afaik) (baseConfig : WalkConfig)
    (observations : Array Expr) : MetaM WalkConfig := do
  let mut refinements := baseConfig.refinements
  for (variableId, value) in ← definitionalRefinements do
    unless refinements.contains variableId do
      refinements := refinements.insert variableId value
  for fact in afaik.facts do
    if let some (variableId, value) ← refinementOf? (← displayedProposition fact) then
      unless refinements.contains variableId do
        refinements := refinements.insert variableId value
  return { baseConfig with
    refinements := refinements
    functionGraphs := true
    observations := observations
    shareSymbolicValues := true }

/-- The selected value before supporting context is added. Atom IDs are shared
    with the full datum, not independently minted for a second visualization. -/
public meta structure InspectedValue where
  root : String
  term : String
  data : JsonDataInstance
  hasStructure : Bool
  facts : Array String
  deriving ToJson, Inhabited

private meta def selectedValueData (root : String) (witnessIds : Array String)
    (data : JsonDataInstance) : JsonDataInstance := Id.run do
  -- Everything emitted by the root walk belongs to the selected expression,
  -- including custom relations and function graphs whose result is last.
  -- Only preallocated witnesses not yet used by that walk are excluded.
  let mut used := (∅ : Std.HashSet String).insert root
  for relation in data.relations do
    for tuple in relation.tuples do
      for atom in tuple.atoms do used := used.insert atom
  return { data with atoms := data.atoms.filter fun atom =>
    !witnessIds.contains atom.id || used.contains atom.id }

/-- Translate proof-backed knowledge into Spytial's relational data. The
    proofs remain owned by IYKYK. Requested observations parameterize the
    expression walk and add their function graphs over every represented value
    of the observer's domain type.
    Alongside the data: the subterm
    behind each atom (see `Provenance`) and the datum a raw Lean selector's
    `Spytial.Sel` form receives — the root with its known refinements
    substituted, closed exactly when the context determines the value. -/
private meta def relationalizeAfaikInspection (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM (JsonDataInstance × Provenance × Expr × InspectedValue) :=
  withoutModifyingEnv do
    let mut config ← contextWalkConfig afaik baseConfig observations
    let refinements := config.refinements
    let root ← if afaik.root.isFVar || afaik.root.isMVar then
      pure afaik.root
    else
      reduceKnown refinements 8 afaik.root observations
    unless observations.isEmpty do
      let (_, discovery) ← StateT.run (s := {}) do
        let mut anchors ← addWitnesses afaik true
        let rootId ← walkExpr config root
        anchors := anchors.push (root, rootId)
        for fact in afaik.facts do
          if let some (variableId, value) ← refinementOf? (← displayedProposition fact) then
            if refinements[variableId]?.any (·.equal value) then continue
          anchors ← walkFact config fact anchors
      config ← prepareObservations config (discovery.observationTerms.map (·.1))
        (afaik.facts.map (·.proof))
    let ((rootId, hasStructure, valueData), state) ← StateT.run (s := {}) do
      -- Witnesses first: a witness can occur inside the refined root, and the
      -- walk reuses its atom only when it is already registered.
      let mut anchors ← addWitnesses afaik (!observations.isEmpty)
      let witnessIds := anchors.map (·.2)
      let rootId ← walkExpr config root
      let rootData := selectedValueData rootId witnessIds (← get).toDataInstance
      let hasStructure := !rootData.relations.isEmpty
      unless anchors.any fun (expression, _) => expression.equal root do
        anchors := anchors.push (root, rootId)
      -- Compute against the already prepared context proofs, but capture the
      -- selected value before context-only structures enter the graph.
      let isSelected := fun (entry : Expr × String) =>
        rootData.atoms.any (·.id == entry.2)
      let deferred := (← get).observationTerms.filter (!isSelected ·)
      modify fun state => { state with observationTerms := state.observationTerms.filter isSelected }
      addActiveDomainObservations config observations
      let valueData := selectedValueData rootId witnessIds (← get).toDataInstance
      modify fun state => { state with observationTerms := state.observationTerms ++ deferred }
      for fact in afaik.facts do
        if let some (variableId, value) ← refinementOf? (← displayedProposition fact) then
          if refinements[variableId]?.any (·.equal value) then continue
        anchors ← walkFact config fact anchors
      addActiveDomainObservations config observations
      return (rootId, hasStructure, valueData)
    let facts ← afaik.facts.mapM fun fact => do
      return (← ppExpr (← displayedProposition fact)).pretty
    let inspection : InspectedValue := {
      root := rootId, term := (← ppExpr afaik.root).pretty
      -- Keep empty declarations for context-only relations: the same checked
      -- layout remains meaningful in either view, with empty selections here.
      data := { valueData with relations := state.toDataInstance.relations.map fun relation =>
        (valueData.relations.find? (·.id == relation.id)).getD { relation with tuples := #[] } }
      hasStructure, facts }
    return (state.toDataInstance, state.provenance,
      substituteKnown refinements 8 afaik.root, inspection)

/-- Translate context knowledge, preserving the original data/provenance API. -/
public meta def relationalizeAfaikWithProvenance (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM (JsonDataInstance × Provenance × Expr) := do
  let (data, prov, datum, _) ← relationalizeAfaikInspection afaik baseConfig observations
  return (data, prov, datum)

/-- `relationalizeAfaikWithProvenance`, data only. -/
public meta def relationalizeAfaik (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM JsonDataInstance :=
  return (← relationalizeAfaikWithProvenance afaik baseConfig observations).1

/-- The status Spytial needs in addition to a successful relational payload. -/
public meta structure ContextViewStatus where
  truncated : Bool := false
  inconsistent : Bool := false
  deriving Inhabited

/-- One successful IYKYK extraction together with Spytial's observation of it. -/
public meta structure ContextView where
  afaik : Iykyk.Afaik
  data : JsonDataInstance
  /-- The subterm behind each atom, for raw Lean selectors. -/
  prov : Provenance
  /-- The value a raw Lean selector's `Spytial.Sel` form receives: the root
      with its known refinements substituted. -/
  datum : Expr
  inspection : InspectedValue
  deriving Inhabited

/-- Local names and their definitions have one spelling for relevance
    matching. This does not unfold observed functions or change their proofs. -/
private meta def contextTerm (cfg : WalkConfig) (e : Expr) : MetaM Expr :=
  normalizeReferenceTerm (substituteKnown cfg.refinements 8 e)

/-- Symbolic data occurrences in a fact, excluding types, proof terms,
    instances, and function heads. Closed scalars such as `0` and `1` are not
    bridges between otherwise unrelated facts, unless explicitly selected. -/
private meta partial def contextualTerms (cfg : WalkConfig) (root e : Expr) :
    MetaM (Std.HashSet ExprStructEq) := do
  let rec visit (e : Expr) : StateT (Std.HashSet ExprStructEq) MetaM Unit := do
    unless e.hasLooseBVars do
      let ty ← inferType e
      if ty.isSort then
        unless ← isProp e do return
      else
        if ← isProofArg e then return
        if (← isClass? ty).isSome then return
        if e.hasFVar || e.hasMVar || e.equal root then
          let key : ExprStructEq := ⟨e⟩
          if (← get).contains key then return
          modify (·.insert key)
    match e with
    | .forallE _ domain body _ => visit domain; visit body
    | .mdata _ body => visit body
    | .proj _ _ body => visit body
    | _ => for argument in e.getAppArgs do visit argument
  let (_, terms) ← (visit (← contextTerm cfg e)).run {}
  return terms

/-- Keep the certified component connected to the values actually represented
    by the selected root. IYKYK still owns extraction and contradiction checks;
    this consumer only selects a subset of its checked facts and witnesses. -/
private meta def projectToRepresentation (afaik : Iykyk.Afaik) (baseConfig : WalkConfig)
    (observations : Array Expr) : MetaM Iykyk.Afaik := withoutModifyingEnv do
  let cfg ← contextWalkConfig afaik { baseConfig with recordTerms := true } observations
  let root ← contextTerm cfg afaik.root
  let (_, state) ← StateT.run (s := {}) do
    -- Preallocate witness identities, but only occurrences visited from the
    -- root enter observationTerms. Unrelated witnesses are not seed anchors.
    let _ ← addWitnesses afaik false
    let _ ← walkExpr cfg (← contextArgument cfg root)
    pure ()
  let mut anchors : Std.HashSet ExprStructEq := {}
  anchors := anchors.insert ⟨root⟩
  for (term, _) in state.observationTerms do
    let term ← contextTerm cfg term
    if term.hasFVar || term.hasMVar then anchors := anchors.insert ⟨term⟩
  let candidates ← afaik.facts.mapM fun fact => do
    contextualTerms cfg root (← displayedProposition fact)
  let mut selected : Std.HashSet Nat := {}
  let mut changed := true
  while changed do
    changed := false
    for index in [:afaik.facts.size] do
      if selected.contains index then continue
      let terms := candidates[index]!
      if terms.toArray.any anchors.contains then
        selected := selected.insert index
        changed := true
        for term in terms do anchors := anchors.insert term
  let kept := afaik.facts.zipIdx |>.filter (fun (_, i) => selected.contains i) |>.map (·.1)
  return afaik.project
    (fun fact => kept.any (·.proposition.equal fact.proposition))
    (fun witness => (root.find? (·.equal witness.term)).isSome ||
      kept.any fun fact => (fact.proposition.find? (·.equal witness.term)).isSome)

/-- Ask IYKYK what is known, then translate a successful result for Spytial. -/
public meta def wdykInContext (subject : Expr) (walkConfig : WalkConfig := {})
    (wdykConfig : Iykyk.Config := {}) (observations : Array Expr := #[]) :
    MetaM (ContextViewStatus × Option ContextView) := do
  match ← Iykyk.wdyk subject { wdykConfig with rootOnly := false } with
  | .inconsistent _ => return ({ inconsistent := true }, none)
  | .afaik afaik =>
      let afaik ← if wdykConfig.rootOnly && !(← isProp (← inferType subject)) then
        projectToRepresentation afaik walkConfig observations
      else pure afaik
      let (data, prov, datum, inspection) ←
        relationalizeAfaikInspection afaik walkConfig observations
      let inspection := { inspection with term := (← ppExpr subject).pretty }
      return ({ truncated := afaik.truncated }, some { afaik, data, prov, datum, inspection })

private meta def isWitnessTerm (afaik : Iykyk.Afaik) (expression : Expr) : Bool :=
  afaik.witnesses.any fun witness => witness.term.equal expression

/-- Relations produced when the expression walker observes named applications. -/
private meta partial def functionGraphScopeEntries (afaik : Iykyk.Afaik) (cfg : WalkConfig)
    (value : Expr) : MetaM (Array (String × Nat) × Array (Option Name)) := do
  let value ← instantiateMVars value
  let value ← if (← observedGraphSide? cfg value).isSome then pure value else whnf value
  if isWitnessTerm afaik value then
    return (#[], #[← typeHead? (← inferType value)])
  let mut relations := #[]
  let mut heads := #[]
  if let some (name, arguments) ← graphSide? value then
    relations := relations.push (name, arguments.size + 1)
    for argument in arguments do
      heads := heads.push (← typeHead? (← inferType argument))
    heads := heads.push (← typeHead? (← inferType value))
  for argument in ← dataArgsOf value do
    let (childRelations, childHeads) ← functionGraphScopeEntries afaik cfg argument
    relations := relations ++ childRelations
    heads := heads ++ childHeads
  return (relations, heads)

/-- Extend the selected value's normal Spytial scope (`base`) with the
    relations that this IYKYK result can emit. -/
public meta def scopeForAfaik (afaik : Iykyk.Afaik) (base : SelScope)
    (observations : Array Expr := #[]) : MetaM SelScope := do
  let cfg : WalkConfig := { functionGraphs := true, observations }
  let mut scope : SelScope := base
  let mut heads := #[]
  let mut relations := #[]
  let (rootRelations, rootHeads) ← functionGraphScopeEntries afaik cfg afaik.root
  relations := relations ++ rootRelations
  heads := heads ++ rootHeads
  for observation in observations do
    let (observationRelations, observationHeads) ←
      functionGraphScopeEntries afaik cfg observation
    relations := relations ++ observationRelations
    heads := heads ++ observationHeads
  for fact in afaik.facts do
    if let some (name, arguments) ← propTupleShape? (← displayedProposition fact) then
      relations := relations.push (name, arguments.size)
      for argument in arguments do
        heads := heads.push (← typeHead? (← inferType argument))
        let (argumentRelations, argumentHeads) ← functionGraphScopeEntries afaik cfg argument
        relations := relations ++ argumentRelations
        heads := heads ++ argumentHeads
  for head in heads.filterMap id do
    scope := scope.merge (← SelScope.ofType head)
  for (name, arity) in relations do
    scope := { scope with rels :=
      match scope.rels.get? name with
      | some (owner, some previous) =>
          if previous == arity then scope.rels else scope.rels.insert name (owner, none)
      | some (_, none) => scope.rels
      | none => scope.rels.insert name (scope.root, some arity) }
  return { scope with lenient := scope.lenient || heads.contains none }

end

end SpytialLean

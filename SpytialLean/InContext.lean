module

public meta import SpytialLean.Context
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.PredicateObservation
public meta import SpytialLean.SelectorElab

namespace SpytialLean

open Lean Meta

public section

/-!
# Inspecting terms in context

Context preparation retains Lean proofs and shared witness terms in their original scope.
This module selects the evidence relevant to the represented values, then interprets supported
proof types as relations, equalities as structural refinements, and requested observations as
computations or focused proof obligations. The same path serves function and theorem inspections.
-/

private meta def isNegation (proposition : Expr) : Bool :=
  match proposition with
  | .app (.const ``Not _) _ => true
  | .forallE _ _ body _ => !body.hasLooseBVar 0 && body.isConstOf ``False
  | _ => false

/-- The implementation output corresponding to the metatheory's checked `Proposition` boundary.
    `head` retains declaration/free-variable identity even when two heads share a display name. -/
public meta structure PropTupleShape where
  relation : String
  head : Expr
  arguments : Array Expr

/-- The positive relation represented by a known proposition. Equations with a
    named application become function-graph tuples. Negative and disjunctive
    knowledge does not produce an unconditional tuple. -/
public meta def propTupleShape? (proposition : Expr) : MetaM (Option PropTupleShape) := do
  unless ← isProp proposition do return none
  if proposition.isAppOfArity ``Or 2 then return none
  if let some (_, domain, result) := proposition.eq? then
    if let some (name, args) ← graphSide? domain then
      return some { relation := name, head := domain.getAppFn, arguments := args.push result }
    if let some (name, args) ← graphSide? result then
      return some { relation := name, head := result.getAppFn, arguments := args.push domain }
  if isNegation proposition then return none
  let some name ← propRelName? proposition.getAppFn | return none
  let args ← dataArgsOf proposition
  if args.isEmpty then return none
  return some { relation := name, head := proposition.getAppFn, arguments := args }

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

/-- Primitive values keep their informative value labels (`3`, `true`, ...)
    when a refinement determines them. Names instead label structured values,
    whose constructor label describes shape rather than contextual identity. -/
private meta def primitiveLabelTypes : List Name :=
  [``Nat, ``String, ``Bool, ``Char, ``Int, ``Float, ``UInt8, ``UInt16,
    ``UInt32, ``UInt64, ``USize]

private meta def isPrimitiveLabelType (ty : Expr) : MetaM Bool := do
  return (← typeHead? ty).any primitiveLabelTypes.contains

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

/-- Find the atom reached by a refined local even when context preparation substituted the
    local before the relational walk saw it. -/
private meta def atomForRefinedLocal? (fvarId : FVarId)
    (refinements : Std.HashMap FVarId Expr) (state : WalkState) : MetaM (Option String) := do
  if let some atomId := state.fvarAtoms[fvarId]? then return some atomId
  let some value := refinements[fvarId]? | return none
  let value ← whnf (substituteKnown refinements 8 value)
  for (term, atomId) in state.selectorTerms do
    let term ← whnf (substituteKnown refinements 8 term)
    if term.equal value then return some atomId
  for (atomId, representative) in state.provenance do
    let representative ← whnf (substituteKnown refinements 8 representative)
    if representative.equal value then return some atomId
  return none

/-- Prefer user-written local names for represented values refined by the
    context. Concrete primitive values keep informative labels such as `3`,
    while a name may replace a generated symbolic primitive label. Later
    declarations are nearer the inspection site and win when several aliases
    denote one atom; the explicitly inspected root wins over every other alias.
    Atom ids, relations, and provenance are unchanged. -/
private meta def labelRefinedLocals (selected : Expr) (rootId : String)
    (refinements : Std.HashMap FVarId Expr) (state : WalkState) : MetaM WalkState := do
  let mut labels : Std.HashMap String String := {}
  let mut generatedRenames : Std.HashMap String String := {}
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail || !refinements.contains declaration.fvarId then
      continue
    let userName := declaration.userName
    if userName.isAnonymous || userName.hasMacroScopes then continue
    if let some atomId ← atomForRefinedLocal? declaration.fvarId refinements state then
      if ← isPrimitiveLabelType declaration.type then
        unless state.generatedAtoms.contains atomId do continue
        let some atom := state.atoms.find? (·.id == atomId) | continue
        generatedRenames := generatedRenames.insert atom.label (toString userName)
      labels := labels.insert atomId (toString userName)
  if let .fvar fvarId := selected then
    let declaration ← fvarId.getDecl
    if !declaration.isImplementationDetail && !(← isPrimitiveLabelType declaration.type) then
      let userName := declaration.userName
      if !userName.isAnonymous && !userName.hasMacroScopes then
        labels := labels.insert rootId (toString userName)
  return { state with atoms := state.atoms.map fun atom =>
    let rewritten := generatedRenames.toArray.foldl
      (fun label (generated, contextual) => label.replace generated contextual) atom.label
    match labels[atom.id]? with
    | some label => { atom with label }
    | none => { atom with label := rewritten } }

private meta def contextArgument (cfg : WalkConfig) (argument : Expr) :
    MetaM Expr :=
  if argument.isFVar || argument.isMVar then pure argument
  else reduceKnown cfg.refinements 8 argument cfg.observations

/-- Recover the proposition in the vocabulary in which its proof was built.
    Preparation normalizes propositions for matching; a consumer should still call
    `x < y` by its source relation `lt`, rather than exposing its reduction to
    `Nat.le (Nat.succ x) y`. -/
private meta def displayedProposition (fact : Expr) : MetaM Expr :=
  do instantiateMVars (← inferType fact)

/-- Recover the user-written binder from the existential proof consumed by a
    witness's `Classical.choose`, when that binder survived elaboration. -/
private meta def witnessBinderName? (term : Expr) : MetaM (Option String) := do
  let some proof := term.getAppArgs.back? | return none
  let proposition ← instantiateMVars (← inferType proof)
  unless proposition.isAppOfArity ``Exists 2 do return none
  let predicate := proposition.getAppArgs[1]!
  let .lam binderName _ _ _ := predicate | return none
  if binderName.isAnonymous || binderName.hasMacroScopes then return none
  return some (toString binderName)

/-- Allocate the shared unknowns before anything else walks. Registering each
    choice term in `applicationAtoms` makes all of its occurrences reuse the
    same atom rather than displaying `Classical.choose`. Prefer the source
    existential's binder; genuinely anonymous witnesses use a neutral name. -/
private meta def addWitnesses (context : InspectionContext) (recordObservationTerms : Bool) :
    StateT WalkState MetaM (Array (Expr × String)) := do
  let mut anchors := #[]
  for witness in context.witnesses do
    -- The walk reduces before its `applicationAtoms` lookup, so an occurrence
    -- inside the root is found under the reduced spelling.
    let reduced ← whnf witness
    let state ← get
    let binderName? ← witnessBinderName? witness
    let (label, state) ← match binderName? with
      | some binderName => pure (state.freshGeneratedLabel binderName)
      | none => pure state.freshAnonymousLabel
    let (atomId, state) := state.freshId
    let atom : JsonAtom := {
      id := atomId
      type := ← sigOfType (← inferType witness)
      label
    }
    set <| ({ state.addAtom atom with
      applicationAtoms :=
        (state.applicationAtoms.insert ⟨witness⟩ atomId).insert ⟨reduced⟩ atomId
      generatedAtoms := state.generatedAtoms.insert atomId
      observationTerms := if recordObservationTerms then
        state.observationTerms.push (witness, atomId)
      else state.observationTerms }).rememberSelectorTerm witness atomId
    anchors := anchors.push (witness, atomId)
  return anchors

/-- Emit one known proposition while reusing atoms already allocated for the
    root, shared witnesses, and repeated relation endpoints. -/
private meta def walkFact (cfg : WalkConfig)
    (fact : Expr) (initialAnchors : Array (Expr × String)) :
    StateT WalkState MetaM (Array (Expr × String)) := do
  let proposition ← displayedProposition fact
  let some shape ← propTupleShape? proposition
    | return initialAnchors
  let relation := shape.relation
  let rawArguments := shape.arguments
  let rawTypes ← rawArguments.mapM fun argument => do
    sigOfType (← inferType argument)
  let relationId ← headRelationId shape.head rawTypes
  -- A checked equation about an observed application names the same output as its
  -- observation. Reuse that result by source expression, rather than walking an
  -- equivalent RHS (e.g. `h + 1` reduced to `Nat.succ h`) into a second value.
  let observedResult? ← do
    if !cfg.observations.any (fun observation => observation.getAppFn.equal shape.head) then
      pure none
    else
      let some (_, lhs, rhs) := proposition.eq? | pure none
      let source := if lhs.getAppFn.equal shape.head then lhs else rhs
      let source ← contextArgument cfg source
      pure (← get).applicationAtoms[(⟨source⟩ : ExprStructEq)]?
  let mut anchors := initialAnchors
  let mut atomIds := #[]
  let mut types := #[]
  for rawArgument in rawArguments do
    let argument ← contextArgument cfg rawArgument
    let mut atomId? := if atomIds.size + 1 == rawArguments.size then observedResult? else none
    for (seen, atomId) in anchors do
      if atomId?.isNone && seen.equal argument then
        atomId? := some atomId
        break
    -- Root and earlier fact walks record every visited subterm, not just their
    -- explicit anchors. A fact about one of those subterms reuses the drawn atom.
    if atomId?.isNone then
      for (seen, atomId) in (← get).selectorTerms do
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
    types := types.push rawTypes[types.size]!
    -- Keep the source term even if a proved equality refined this endpoint.
    modify fun state => state.rememberSelectorTerm rawArgument atomId
  -- An observation may already have emitted the graph point established by
  -- this equation. Relations contain tuples, not one copy per justification.
  unless ((← get).relations[relationId]?).any (fun stored =>
      stored.tuples.any (·.atoms == atomIds)) do
    modify fun state => state.addTuple relation types { atoms := atomIds, types } relationId
  return anchors

private meta def contextWalkConfig (context : InspectionContext) (baseConfig : WalkConfig)
    (observations : Array Expr) : MetaM WalkConfig := do
  let mut refinements := baseConfig.refinements
  for (variableId, value) in ← definitionalRefinements do
    unless refinements.contains variableId do
      refinements := refinements.insert variableId value
  for fact in context.proofs do
    if let some (variableId, value) ← refinementOf? (← displayedProposition fact) then
      unless refinements.contains variableId do
        refinements := refinements.insert variableId value
  let candidateRefinements := refinements
  for (variableId, _) in candidateRefinements.toArray do
    if refinementIsCyclic candidateRefinements variableId then
      refinements := refinements.erase variableId
  return { baseConfig with
    refinements := refinements
    functionGraphs := true
    observations := observations
    shareSymbolicValues := true }

/-- Metadata shown alongside one context-informed inspection. -/
public meta structure InspectedValue where
  root : String
  term : String
  facts : Array String
  deriving ToJson, Inhabited

private meta def rootWalkAtomIds (root : String) (witnessIds : Array String)
    (data : JsonDataInstance) : Std.HashSet String := Id.run do
  -- Preallocated witnesses used by the root walk belong with the root's other
  -- terms. Unused witnesses are deferred so their observations follow the fact
  -- that introduced them, preserving the full datum's stable walk order.
  let mut used := (∅ : Std.HashSet String).insert root
  for relation in data.relations do
    for tuple in relation.tuples do
      for atom in tuple.atoms do used := used.insert atom
  return data.atoms.foldl (init := ∅) fun atoms atom =>
    if !witnessIds.contains atom.id || used.contains atom.id then atoms.insert atom.id
    else atoms

/-- Simplify observations, ask Lean only the focused questions exposed by
    remaining arithmetic blockers, and simplify again with every checked
    answer. The loop is local and bounded; unanswered questions remain
    symbolic. -/
private meta def prepareContextObservations (context : InspectionContext) (config : WalkConfig)
    (domain : Array Expr) : MetaM WalkConfig := do
  let contextProofs := context.proofs
  let queryEvidence ← preparePredicateEvidence { proofs := contextProofs }
  let mut prepared ← prepareObservations config domain contextProofs
  let mut answers : Array Expr := #[]
  let mut answered : Std.HashSet ExprStructEq := {}
  let mut attempted : Std.HashSet ExprStructEq := {}
  let mut warnedAboutBudget := false
  for _ in [:4] do
    let mut changed := false
    for question in ← observationQuestions prepared do
      if question.alternatives.any (fun goal => answered.contains ⟨goal⟩) then continue
      for goal in question.alternatives do
        if attempted.contains ⟨goal⟩ then continue
        attempted := attempted.insert ⟨goal⟩
        let attempt ← if let some proof ← provePredicate? queryEvidence goal then
          pure (ProofAttempt.proved proof)
        else proveArithmetic contextProofs goal
        match attempt with
        | .proved proof =>
            answers := answers.push proof
            answered := answered.insert ⟨goal⟩
            changed := true
            break
        | .notProved => pure ()
        | .truncated =>
            unless warnedAboutBudget do
              logWarning "spytial: an observation proof query exhausted its arithmetic budget; \
                leaving the affected computation symbolic"
              warnedAboutBudget := true
    unless changed do return prepared
    prepared ← prepareObservations
      { prepared with observationResults := {}, observationResiduals := {} }
      domain (contextProofs ++ answers)
  return prepared

/-- A local equation such as `height t = k + 1` gives the value of an unobserved
    numeric call. Every occurrence of the call is then drawn as that value, with
    the equation as its proof, instead of being unfolded into its definition. -/
private meta def addEquationResults (context : InspectionContext) (config : WalkConfig) :
    MetaM WalkConfig := do
  let mut results := config.observationResults
  for fact in context.proofs do
    let some (_, lhs, rhs) := (← displayedProposition fact).eq? | continue
    let (call, value, proof) ←
      if (← graphSide? lhs).isSome then pure (lhs, rhs, fact)
      else if (← graphSide? rhs).isSome then pure (rhs, lhs, ← mkEqSymm fact)
      else continue
    unless call.hasFVar || call.hasMVar do continue
    if results.contains ⟨call⟩ then continue
    if config.observations.any (·.getAppFn.equal call.getAppFn) then continue
    if (value.find? (·.equal call)).isSome then continue
    unless ← isPrimitiveLabelType (← inferType call) do continue
    results := results.insert ⟨call⟩ { expr := value, proof? := some proof }
  return { config with observationResults := results }

/-- Translate local evidence into Spytial's relational data. The proof types determine which
    relations and refinements can be displayed. Requested observations parameterize the
    expression walk and add their function graphs over every represented value
    of the observer's domain type.
    Alongside the data: the subterm
    behind each atom (see `Provenance`) and the datum a raw Lean selector's
    `Spytial.Sel` form receives — the root with its known refinements
    substituted, closed exactly when the context determines the value. -/
private meta def relationalizeContextInspection (context : InspectionContext)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[])
    (selectedRoot? : Option Expr := none) :
    MetaM (JsonDataInstance × Provenance × Expr × InspectedValue × SelectorEvidence) :=
  withoutModifyingEnv <| withLCtx context.scope context.localInstances do
    -- Programmatic callers can construct the record. Validate their proof terms too;
    -- the record's type is not a replacement for checking evidence.
    for proof in context.proofs do
      discard <| checkInspectionProof (← inferType proof) proof
    let mut config ← contextWalkConfig context
      { baseConfig with recordSelectorTerms := true } observations
    let refinements := config.refinements
    let root ← if context.root.isFVar || context.root.isMVar then
      pure context.root
    else
      reduceKnown refinements 8 context.root observations
    unless observations.isEmpty do
      let (_, discovery) ← StateT.run (s := {}) do
        let mut anchors ← addWitnesses context true
        let rootId ← walkExpr config root
        anchors := anchors.push (root, rootId)
        for fact in context.proofs do
          if let some (variableId, value) ← refinementOf? (← displayedProposition fact) then
            if refinements[variableId]?.any (·.equal value) then continue
          anchors ← walkFact config fact anchors
      config ← prepareContextObservations context config (discovery.observationTerms.map (·.1))
    config ← addEquationResults context config
    let (rootId, state) ← StateT.run (s := {}) do
      -- Witnesses first: a witness can occur inside the refined root, and the
      -- walk reuses its atom only when it is already registered.
      let mut anchors ← addWitnesses context (!observations.isEmpty)
      let witnessIds := anchors.map (·.2)
      let rootId ← walkExpr config root
      modify fun state => state.rememberSelectorTerm context.root rootId
      unless anchors.any fun (expression, _) => expression.equal root do
        anchors := anchors.push (root, rootId)
      -- Emit root-walk observations before relations introduced by facts.
      let rootAtoms := rootWalkAtomIds rootId witnessIds (← get).toDataInstance
      let belongsToRootWalk := fun (entry : Expr × String) =>
        rootAtoms.contains entry.2
      let deferred := (← get).observationTerms.filter (!belongsToRootWalk ·)
      modify fun state => {
        state with observationTerms := state.observationTerms.filter belongsToRootWalk }
      addActiveDomainObservations config observations
      modify fun state => { state with observationTerms := state.observationTerms ++ deferred }
      for fact in context.proofs do
        if let some (variableId, value) ← refinementOf? (← displayedProposition fact) then
          if refinements[variableId]?.any (·.equal value) then continue
        anchors ← walkFact config fact anchors
      addActiveDomainObservations config observations
      return rootId
    let state ← labelRefinedLocals (selectedRoot?.getD context.root) rootId refinements state
    let facts ← context.proofs.mapM fun fact => do
      return (← ppExpr (← displayedProposition fact)).pretty
    let inspection : InspectedValue := {
      root := rootId, term := (← ppExpr context.root).pretty, facts }
    return (state.toDataInstance, state.provenance,
      substituteKnown refinements 8 context.root, inspection, {
        terms := state.selectorTerms
        proofs := context.proofs ++
          config.observationResults.toArray.filterMap (·.2.proof?) })

/-- Translate context knowledge, preserving the original data/provenance API. -/
public meta def relationalizeContextWithProvenance (context : InspectionContext)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM (JsonDataInstance × Provenance × Expr) := do
  let (data, prov, datum, _, _) ← relationalizeContextInspection context baseConfig observations
  return (data, prov, datum)

/-- `relationalizeContextWithProvenance`, data only. -/
public meta def relationalizeContext (context : InspectionContext)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM JsonDataInstance :=
  return (← relationalizeContextWithProvenance context baseConfig observations).1

/-- The status Spytial needs in addition to a successful relational payload. -/
public meta structure ContextViewStatus where
  truncated : Bool := false
  inconsistent : Bool := false
  deriving Inhabited

/-- A prepared context together with its relational inspection. -/
public meta structure ContextView where
  context : InspectionContext
  data : JsonDataInstance
  /-- The subterm behind each atom, for raw Lean selectors. -/
  prov : Provenance
  /-- The value a raw Lean selector's `Spytial.Sel` form receives: the root
      with its known refinements substituted. -/
  datum : Expr
  inspection : InspectedValue
  /-- Terms and certified evidence interpreting the atoms in `data`. -/
  evidence : SelectorEvidence

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

/-- Whether `e` is a constructor-built value of a recursive inductive. Such a
    value contributes another instance of the selected representation's shape,
    rather than merely an opaque endpoint or scalar fact. -/
private meta def recursiveConstructorValue? (e : Expr) : MetaM (Option (Name × Expr)) := do
  let type ← inferType e
  if ← isPrimitiveLabelType type then return none
  let some typeName ← typeHead? type | return none
  let some shape ← TypeShape.ofInductive typeName | return none
  unless shape.ctors.any (fun ctor =>
      ctor.fields.any (fun field => field.typeHead == some typeName)) do
    return none
  let value ← whnf e
  let .const ctorName _ := value.getAppFn | return none
  unless shape.ctors.any (·.ctorName == ctorName) do return none
  return some (typeName, value)

/-- A root-only fact must not extend an explicit observation to an alternate
    constructor-built recursive value when the selected representation already
    contains that recursive type. Opaque endpoints remain admissible, as do
    observations wholly about represented subterms. -/
private meta partial def observesAlternateRecursiveValue (cfg : WalkConfig)
    (representedTerms : Std.HashSet ExprStructEq)
    (representedTypes : Std.HashSet Name)
    (expression : Expr) : MetaM Bool := do
  let expression ← contextTerm cfg expression
  if let some (_, arguments) ← observedGraphSide? cfg expression then
    for argument in arguments do
      let argument ← contextTerm cfg argument
      unless representedTerms.contains ⟨argument⟩ do
        if let some (typeName, value) ← recursiveConstructorValue? argument then
          if !representedTerms.contains ⟨value⟩ && representedTypes.contains typeName then
            return true
  for argument in ← dataArgsOf expression do
    if ← observesAlternateRecursiveValue cfg representedTerms representedTypes argument then
      return true
  return false

/-- Keep the certified component connected to the values actually represented
    by the selected root. Preparation has already checked the proofs and contradictions;
    projection only selects a subset of the retained proofs and witness terms. -/
private meta def projectToRepresentation (context : InspectionContext) (baseConfig : WalkConfig)
    (observations : Array Expr) : MetaM InspectionContext := withoutModifyingEnv do
  let cfg ← contextWalkConfig context { baseConfig with recordTerms := true } observations
  let root ← contextTerm cfg context.root
  let (_, state) ← StateT.run (s := {}) do
    -- Preallocate witness identities, but only occurrences visited from the
    -- root enter observationTerms. Unrelated witnesses are not seed anchors.
    let _ ← addWitnesses context false
    let _ ← walkExpr cfg (← contextArgument cfg root)
    pure ()
  let mut anchors : Std.HashSet ExprStructEq := {}
  anchors := anchors.insert ⟨root⟩
  let mut representedTerms : Std.HashSet ExprStructEq := {}
  let mut representedTypes : Std.HashSet Name := {}
  for (term, _) in state.observationTerms do
    let term ← contextTerm cfg term
    representedTerms := representedTerms.insert ⟨term⟩
    if let some typeName ← typeHead? (← inferType term) then
      representedTypes := representedTypes.insert typeName
    if term.hasFVar || term.hasMVar then anchors := anchors.insert ⟨term⟩
  for (_, representative) in state.provenance do
    let representative ← contextTerm cfg representative
    representedTerms := representedTerms.insert ⟨representative⟩
    if let some typeName ← typeHead? (← inferType representative) then
      representedTypes := representedTypes.insert typeName
  representedTerms := representedTerms.insert ⟨root⟩
  if let some typeName ← typeHead? (← inferType root) then
    representedTypes := representedTypes.insert typeName
  let candidates ← context.proofs.mapM fun fact => do
    contextualTerms cfg root (← displayedProposition fact)
  let mut stale : Array Bool := #[]
  for index in [:context.proofs.size] do
    let proposition ← displayedProposition context.proofs[index]!
    let isRefinement := (← refinementOf? proposition).isSome
    let isStale ← if isRefinement then pure false else
      observesAlternateRecursiveValue cfg representedTerms representedTypes proposition
    stale := stale.push isStale
  let mut selected : Std.HashSet Nat := {}
  let mut changed := true
  while changed do
    changed := false
    for index in [:context.proofs.size] do
      if selected.contains index || stale[index]! then continue
      let terms := candidates[index]!
      if terms.toArray.any anchors.contains then
        selected := selected.insert index
        changed := true
        for term in terms do anchors := anchors.insert term
  let proofs := context.proofs.zipIdx |>.filter (fun (_, i) => selected.contains i) |>.map (·.1)
  let propositions ← proofs.mapM displayedProposition
  return { context with proofs, witnesses := context.witnesses.filter (fun witness =>
    (root.find? (·.equal witness)).isSome ||
      propositions.any (fun proposition => (proposition.find? (·.equal witness)).isSome)) }

/-- Enrich the local context with standard proof-producing operations, then select and interpret
    the evidence relevant to this inspection. The caller's proof state is unchanged. -/
public meta def inspectInContext (subject : Expr) (walkConfig : WalkConfig := {})
    (inspectionConfig : InspectionConfig := {}) (observations predicates : Array Expr := #[]) :
    MetaM (ContextViewStatus × Option ContextView) := do
  let context ← prepareInspectionContext subject inspectionConfig
  if context.contradiction?.isSome then return ({ inconsistent := true }, none)
  withLCtx context.scope context.localInstances do
    let context ← if inspectionConfig.rootOnly && !(← isProp (← inferType subject)) then
      projectToRepresentation context walkConfig observations
    else pure context
    let (data, prov, datum, inspection, evidence) ←
      relationalizeContextInspection context walkConfig observations (some subject)
    let (data, evidence) ← observePredicates ⟨datum, data, prov, evidence, inspection.root⟩ predicates
    let inspection := { inspection with term := (← ppExpr subject).pretty }
    return ({ truncated := context.truncated },
      some { context, data, prov, datum, inspection, evidence })

private meta def isWitnessTerm (context : InspectionContext) (expression : Expr) : Bool :=
  context.witnesses.any fun witness => witness.equal expression

/-- Relations produced when the expression walker observes named applications. -/
private meta partial def functionGraphScopeEntries (context : InspectionContext) (cfg : WalkConfig)
    (value : Expr) : MetaM (Array (String × Nat) × Array (Option Name)) := do
  let value ← instantiateMVars value
  -- Match the walker: observed calls and unobserved numeric calls over symbolic
  -- arguments stay graph points, so their relations belong in scope.
  let keep := (← observedGraphSide? cfg value).isSome ||
    (← keepsSymbolicCall { cfg with shareSymbolicValues := true } value)
  let value ← if keep then pure value else whnf value
  if isWitnessTerm context value then
    return (#[], #[← typeHead? (← inferType value)])
  let mut relations := #[]
  let mut heads := #[]
  if let some (name, arguments) ← graphSide? value then
    -- Arithmetic is drawn inside value labels, so its operators are not relations.
    unless isArithmeticApplication value && (← isPrimitiveLabelType (← inferType value)) do
      relations := relations.push (name, arguments.size + 1)
    for argument in arguments do
      heads := heads.push (← typeHead? (← inferType argument))
    heads := heads.push (← typeHead? (← inferType value))
  for argument in ← dataArgsOf value do
    let (childRelations, childHeads) ← functionGraphScopeEntries context cfg argument
    relations := relations ++ childRelations
    heads := heads ++ childHeads
  return (relations, heads)

/-- Extend the inspected expression's normal Spytial scope (`base`) with the
    relations that these proof types and observation terms can emit. -/
public meta def scopeForContext (context : InspectionContext) (base : SelScope)
    (observations : Array Expr := #[]) : MetaM SelScope := do
  let cfg : WalkConfig := { functionGraphs := true, observations }
  let mut scope : SelScope := base
  let mut heads := #[]
  let mut relations := #[]
  let (rootRelations, rootHeads) ← functionGraphScopeEntries context cfg context.root
  relations := relations ++ rootRelations
  heads := heads ++ rootHeads
  for observation in observations do
    let (observationRelations, observationHeads) ←
      functionGraphScopeEntries context cfg observation
    relations := relations ++ observationRelations
    heads := heads ++ observationHeads
  for fact in context.proofs do
    if let some shape ← propTupleShape? (← displayedProposition fact) then
      relations := relations.push (shape.relation, shape.arguments.size)
      for argument in shape.arguments do
        heads := heads.push (← typeHead? (← inferType argument))
        let (argumentRelations, argumentHeads) ← functionGraphScopeEntries context cfg argument
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

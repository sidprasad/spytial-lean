module

public meta import Iykyk.Query
public import SpytialLean.Types
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

/-- Which of the two proposition-decoding rules produced a tuple. -/
public inductive PropositionTupleKind where
  /-- A positive predicate application such as `edge x y`. -/
  | predicate
  /-- An equation used as a function-graph point. The Boolean is true when
      the application was the left side of the source equation. -/
  | graph (application result : Expr) (applicationOnLeft : Bool)

/-- The relation and columns decoded from a proposition. The head expression
    is retained because the short display name need not uniquely identify a
    Lean predicate. -/
public structure PropositionTupleShape where
  kind : PropositionTupleKind
  name : String
  head : Expr
  parameters : Array Expr
  arguments : Array Expr

private meta def relationParametersOf (application : Expr) : MetaM (Array Expr) := do
  let arguments := application.getAppArgs
  let dataIndexes ← dataArgumentIndexesOf application
  let mut parameters := #[]
  for index in [:arguments.size] do
    unless dataIndexes.contains index do
      parameters := parameters.push arguments[index]!
  return parameters

/-- The positive relation represented by a known proposition. Equations with a
    named application become function-graph tuples. Negative and disjunctive
    knowledge does not produce an unconditional tuple. -/
public meta def propositionTupleShape? (proposition : Expr) :
    MetaM (Option PropositionTupleShape) := do
  unless ← isProp proposition do return none
  if proposition.isAppOfArity ``Or 2 then return none
  if let some (_, domain, result) := proposition.eq? then
    if let some (name, args) ← graphSide? domain then
      return some {
        kind := .graph domain result true
        name
        head := domain.getAppFn
        parameters := ← relationParametersOf domain
        arguments := args.push result }
    if let some (name, args) ← graphSide? result then
      return some {
        kind := .graph result domain false
        name
        head := result.getAppFn
        parameters := ← relationParametersOf result
        arguments := args.push domain }
  if isNegation proposition then return none
  let head := proposition.getAppFn
  let some name ← propRelName? head | return none
  let args ← dataArgsOf proposition
  if args.isEmpty then return none
  return some {
    kind := .predicate
    name
    head
    parameters := ← relationParametersOf proposition
    arguments := args }

/-- Compatibility projection used by callers that only need the display name
    and decoded columns. New semantic code should use
    `propositionTupleShape?` so it retains the actual relation head. -/
public meta def propTupleShape? (proposition : Expr) : MetaM (Option (String × Array Expr)) := do
  return (← propositionTupleShape? proposition).map fun shape =>
    (shape.name, shape.arguments)

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

/-- Find the atom reached by a refined local even when IYKYK substituted the
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
    IYKYK normalizes propositions for matching; a consumer should still call
    `x < y` by its source relation `lt`, rather than exposing its reduction to
    `Nat.le (Nat.succ x) y`. -/
private meta def displayedProposition (fact : Iykyk.KnownFact) : MetaM Expr :=
  do instantiateMVars (← inferType fact.proof)

/-- An equality retained by IYKYK and checked against the refined expression
    represented by the computation phase of proof-guided inspection. The constructor
    is private; `CheckedEqualityRefinement.check` checks the proof, equality
    shape, term types, and definitional equality of the retained value and
    computed expression. -/
public structure CheckedEqualityRefinement (knowledge : Iykyk.Afaik)
    (_computed : Expr) where
  private mk ::
  factIndex : Fin knowledge.facts.size
  proposition : Expr
  type : Expr
  value : Expr

namespace CheckedEqualityRefinement

/-- The retained IYKYK fact selected by a checked equality refinement. -/
@[expose] public def fact {knowledge : Iykyk.Afaik} {computed : Expr}
    (checked : CheckedEqualityRefinement knowledge computed) : Iykyk.KnownFact :=
  knowledge.facts[checked.factIndex]

private meta partial def find? (knowledge : Iykyk.Afaik) (computed : Expr)
    (index : Nat) : MetaM (Option (CheckedEqualityRefinement knowledge computed)) := do
  if inBounds : index < knowledge.facts.size then
    let fact := knowledge.facts[index]
    let proposition ← displayedProposition fact
    if let some (type, left, right) := proposition.eq? then
      let candidate? :=
        if left.equal knowledge.root then some right
        else if right.equal knowledge.root then some left
        else none
      if let some value := candidate? then
        let rootType ← inferType knowledge.root
        let valueType ← inferType value
        let computedType ← inferType computed
        if (← isDefEq rootType type) && (← isDefEq valueType type) &&
            (← isDefEq computedType type) && (← isDefEq value computed) then
          Iykyk.checkEvidence proposition fact.proof
          return some (.mk ⟨index, inBounds⟩ proposition type value)
    find? knowledge computed (index + 1)
  else
    return none

/-- Select and recheck an equality that relates the inspected root to the
    expression used by the retained computation phase. -/
public meta def check (knowledge : Iykyk.Afaik) (computed : Expr) :
    MetaM (CheckedEqualityRefinement knowledge computed) := do
  let some checked ← find? knowledge computed 0
    | throwError "spytial: no checked equality relates the inspected root to its computation"
  return checked

end CheckedEqualityRefinement

/-- Evidence that ordinary Lean computation identifies the selected root with
    the expression represented by the structural walk. -/
public structure CheckedComputedValue (knowledge : Iykyk.Afaik)
    (_computed : Expr) where
  private mk ::
  type : Expr

namespace CheckedComputedValue

private meta def check? (knowledge : Iykyk.Afaik) (computed : Expr) :
    MetaM (Option (CheckedComputedValue knowledge computed)) := do
  let rootType ← inferType knowledge.root
  let computedType ← inferType computed
  unless ← isDefEq rootType computedType do return none
  unless ← isDefEq knowledge.root computed do return none
  return some (.mk rootType)

end CheckedComputedValue

/-- Why the production inspector accepts one common root/computed type. -/
public inductive CheckedValueReason (knowledge : Iykyk.Afaik)
    (computed : Expr) : Expr → Type where
  | computation (checked : CheckedComputedValue knowledge computed)
    : CheckedValueReason knowledge computed checked.type
  | proof (checked : CheckedEqualityRefinement knowledge computed)
    : CheckedValueReason knowledge computed checked.type

/-- How the production inspector knows the expression represented by its
    structural walk: either by computation or by a retained checked equality. -/
public structure CheckedValueSource (knowledge : Iykyk.Afaik) (computed : Expr) where
  type : Expr
  reason : CheckedValueReason knowledge computed type

namespace CheckedValueSource

/-- Check the computation case first, then look for a retained equality. -/
public meta def check (knowledge : Iykyk.Afaik) (computed : Expr) :
    MetaM (CheckedValueSource knowledge computed) := do
  if let some checked ← CheckedComputedValue.check? knowledge computed then
    return .mk checked.type (.computation checked)
  let checked ← CheckedEqualityRefinement.check knowledge computed
  return .mk checked.type (.proof checked)

end CheckedValueSource

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
private meta def addWitnesses (afaik : Iykyk.Afaik) (recordObservationTerms : Bool) :
    StateT WalkState MetaM (Array (Expr × String)) := do
  let mut anchors := #[]
  for witness in afaik.witnesses do
    -- The walk reduces before its `applicationAtoms` lookup, so an occurrence
    -- inside the root is found under the reduced spelling.
    let reduced ← whnf witness.term
    let state ← get
    let binderName? ← witnessBinderName? witness.term
    let (label, state) ← match binderName? with
      | some binderName => pure (state.freshGeneratedLabel binderName)
      | none => pure state.freshAnonymousLabel
    let (atomId, state) := state.freshId
    let atom : JsonAtom := {
      id := atomId
      type := ← sigOfType witness.type
      label
    }
    set <| ({ state.addAtom atom with
      applicationAtoms :=
        (state.applicationAtoms.insert ⟨witness.term⟩ atomId).insert ⟨reduced⟩ atomId
      generatedAtoms := state.generatedAtoms.insert atomId
      observationTerms := if recordObservationTerms then
        state.observationTerms.push (witness.term, atomId)
      else state.observationTerms }).rememberSelectorTerm witness.term atomId
    anchors := anchors.push (witness.term, atomId)
  return anchors

/-- Emit one known proposition while reusing atoms already allocated for the
    root, shared witnesses, and repeated relation endpoints. -/
private meta def walkFact (cfg : WalkConfig)
    (fact : Iykyk.KnownFact) (initialAnchors : Array (Expr × String)) :
    StateT WalkState MetaM (Array (Expr × String)) := do
  let proposition ← displayedProposition fact
  let some (relation, rawArguments) ← propTupleShape? proposition
    | return initialAnchors
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
    types := types.push (← sigOfType (← inferType argument))
    -- Keep the source term even if a proved equality refined this endpoint.
    modify fun state => state.rememberSelectorTerm rawArgument atomId
  let tuple := { atoms := atomIds, types }
  let origin := .proved proposition fact.proof rawArguments
  -- An observation may already have emitted the graph point established by
  -- this equation. Relations contain one tuple but the trace retains both
  -- justifications.
  if let some (_, tuples) := (← get).relations.get? relation then
    if let some existing := tuples.find? (·.atoms == atomIds) then
      modify fun state => state.addTupleOrigin relation existing origin
      return anchors
  modify fun state => state.addTupleWithOrigin relation types tuple origin
  return anchors

/-- The checked information retained for one production `proved` origin.
    The constructor is private: values come from `checkedProvedOrigins`, which
    rechecks the proof, decoder, types, and term-to-atom links. -/
public structure CheckedProvedOrigin where
  private mk ::
  emission : TupleEmission
  relation : String
  kind : PropositionTupleKind
  head : Expr
  parameters : Array Expr
  proposition : Expr
  proof : Expr
  terms : Array Expr
  origin_eq : emission.origin = .proved proposition proof terms
  columns : CheckedColumns terms.toList emission.tuple.atoms.toList

namespace CheckedProvedOrigin

/-- The inferred Lean type of each checked proof-origin column. -/
@[expose] public def types (origin : CheckedProvedOrigin) : Array Expr :=
  origin.columns.types.toArray

/-- The production atom IDs indexed by the checked columns. -/
@[expose] public def atoms (origin : CheckedProvedOrigin) : Array String :=
  origin.emission.tuple.atoms

end CheckedProvedOrigin

private meta def selectorEvidenceNames (evidence : SelectorEvidence)
    (term : Expr) (atom : String) : Bool :=
  evidence.terms.any fun (knownTerm, knownAtom) =>
    knownAtom == atom && knownTerm.equal term

private meta def checkProvedEmission (emission : TupleEmission)
    (evidence? : Option SelectorEvidence) : MetaM (Option CheckedProvedOrigin) := do
  match originEq : emission.origin with
  | .proved proposition proof terms => do
      Iykyk.checkEvidence proposition proof
      let some shape ← propositionTupleShape? proposition
        | throwError "spytial: a proof origin has no supported relational decoding"
      unless shape.name == emission.relation do
        throwError "spytial: a proof origin changed relation name"
      unless shape.arguments.size == terms.size &&
          (shape.arguments.zip terms).all fun (decoded, recorded) => decoded.equal recorded do
        throwError "spytial: a proof origin changed its relational arguments"
      let some columns ← CheckedColumns.check terms.toList emission.tuple.atoms.toList
        | throwError "spytial: a proof origin is not aligned with its tuple columns"
      let types := columns.types.toArray
      let inferredLabels ← types.mapM sigOfType
      unless inferredLabels == emission.tuple.types do
        throwError "spytial: a proof origin changed its relational column types"
      if let some evidence := evidence? then
        for (term, atom) in terms.zip emission.tuple.atoms do
          unless selectorEvidenceNames evidence term atom do
            throwError "spytial: a proof-origin term does not name its recorded atom"
      return some {
        emission
        origin_eq := originEq
        relation := shape.name
        kind := shape.kind
        head := shape.head
        parameters := shape.parameters
        proposition
        proof
        terms
        columns }
  | _ => return none

/-- Recheck every production `proved` origin and return the actual Lean
    expressions needed by the semantic decoder. In addition to proof and type
    checking, every decoded term must name the recorded tuple atom in the
    selector evidence produced by the same walk. -/
public meta def checkedProvedOrigins (trace : TracedDataInstance)
    (evidence : SelectorEvidence) : MetaM (Array CheckedProvedOrigin) := do
  let mut checked := #[]
  for emission in trace.emissions do
    if let some origin ← checkProvedEmission emission (some evidence) then
      checked := checked.push origin
  return checked

/-- The result of checking every `proved` origin against the trace and the
    selector evidence produced by the same relationalization run. -/
public structure CheckedProofTrace (trace : TracedDataInstance) where
  private mk ::
  origins : Array CheckedProvedOrigin

/-- Run the complete production check for proof-derived tuple origins. -/
public meta def checkProofTrace (trace : TracedDataInstance)
    (evidence : SelectorEvidence) : MetaM (CheckedProofTrace trace) := do
  return { origins := ← checkedProvedOrigins trace evidence }

/-- Compatibility checker for callers that do not retain selector evidence.
    The production proof-context path uses the stronger
    `checkedProvedOrigins` check above. -/
public meta def validateProvedOrigins (trace : TracedDataInstance) : MetaM Unit := do
  for emission in trace.emissions do
    let _ ← checkProvedEmission emission none

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

/-- The two phases of one proof-guided inspection. `computedTrace` is the
    snapshot immediately after the ordinary expression walker has inspected
    the refined root. `trace` extends that state with facts from the context.
    The public JSON result remains `trace.data`. -/
public meta structure ProofGuidedTrace (_knowledge : Iykyk.Afaik) where
  private mk ::
  trace : TracedDataInstance
  provenance : Provenance
  /-- The refined expression represented by the ordinary structural walk. -/
  computedTerm : Expr
  computedTrace : TracedDataInstance
  computedProvenance : Provenance
  computedEvidence : SelectorEvidence
  computedChecked : CheckedStructuralTrace computedTrace
  structuralChecked : CheckedStructuralTrace trace
  proofsChecked : CheckedProofTrace trace
  datum : Expr
  inspection : InspectedValue
  evidence : SelectorEvidence

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

/-- Simplify observations, ask IYKYK only the focused questions exposed by
    remaining arithmetic blockers, and simplify again with every checked
    answer. The loop is local and bounded; unanswered questions remain
    symbolic. -/
private meta def prepareContextObservations (afaik : Iykyk.Afaik) (config : WalkConfig)
    (domain : Array Expr) : MetaM WalkConfig := do
  let contextProofs := afaik.facts.map (·.proof)
  let mut prepared ← prepareObservations config domain contextProofs
  let mut answers : Array Iykyk.KnownFact := #[]
  let mut attempted : Std.HashSet ExprStructEq := {}
  let mut warnedAboutBudget := false
  for _ in [:4] do
    let mut changed := false
    for question in ← observationQuestions prepared do
      if question.alternatives.any fun goal =>
          answers.any fun answer => answer.proposition.equal goal then
        continue
      for goal in question.alternatives do
        if attempted.contains ⟨goal⟩ then continue
        attempted := attempted.insert ⟨goal⟩
        match ← Iykyk.prove afaik goal { mechanisms := #[.simp, .omega] } with
        | .proved fact =>
            answers := answers.push fact
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
      domain (contextProofs ++ answers.map (·.proof))
  return prepared

/-- Translate proof-backed knowledge into Spytial's relational data. The
    proofs remain owned by IYKYK. Requested observations parameterize the
    expression walk and add their function graphs over every represented value
    of the observer's domain type.
    Alongside the data: the subterm
    behind each atom (see `Provenance`) and the datum a raw Lean selector's
    `Spytial.Sel` form receives — the root with its known refinements
    substituted, closed exactly when the context determines the value. -/
private meta def relationalizeAfaikInspectionWithTrace (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[])
    (selectedRoot? : Option Expr := none) :
    MetaM (ProofGuidedTrace afaik) :=
  withoutModifyingEnv do
    let mut config ← contextWalkConfig afaik
      { baseConfig with recordSelectorTerms := true } observations
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
      config ← prepareContextObservations afaik config (discovery.observationTerms.map (·.1))
    let ((rootId, computedState), state) ← StateT.run (s := {}) do
      -- Witnesses first: a witness can occur inside the refined root, and the
      -- walk reuses its atom only when it is already registered.
      let mut anchors ← addWitnesses afaik (!observations.isEmpty)
      let witnessIds := anchors.map (·.2)
      let rootId ← walkExpr config root
      modify fun state => state.rememberSelectorTerm afaik.root rootId
      let computedState ← get
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
      for fact in afaik.facts do
        if let some (variableId, value) ← refinementOf? (← displayedProposition fact) then
          if refinements[variableId]?.any (·.equal value) then continue
        anchors ← walkFact config fact anchors
      addActiveDomainObservations config observations
      return (rootId, computedState)
    let state ← labelRefinedLocals (selectedRoot?.getD afaik.root) rootId refinements state
    let facts ← afaik.facts.mapM fun fact => do
      return (← ppExpr (← displayedProposition fact)).pretty
    let inspection : InspectedValue := {
      root := rootId, term := (← ppExpr afaik.root).pretty, facts }
    let trace := state.toTracedDataInstance
    unless trace.wellFormedTrace do
      throwError "spytial: internal error: malformed proof-context tuple trace"
    let evidence : SelectorEvidence := {
      terms := state.selectorTerms
      proofs := afaik.facts.map (·.proof) ++
        config.observationResults.toArray.filterMap (·.2.proof?) }
    let computedTrace := computedState.toTracedDataInstance
    unless computedTrace.wellFormedTrace do
      throwError "spytial: internal error: malformed computed root tuple trace"
    let computedEvidence : SelectorEvidence := {
      terms := computedState.selectorTerms
      proofs := config.observationResults.toArray.filterMap (·.2.proof?) }
    let datum := substituteKnown refinements 8 afaik.root
    let computedChecked ←
      checkStructuralTrace config computedTrace computedState.provenance computedEvidence
    let structuralChecked ← checkStructuralTrace config trace state.provenance evidence
    let proofsChecked ← checkProofTrace trace evidence
    return {
      trace
      provenance := state.provenance
      computedTerm := datum
      computedTrace
      computedProvenance := computedState.provenance
      computedEvidence
      computedChecked
      structuralChecked
      proofsChecked
      datum
      inspection
      evidence }

/-- Run proof-guided inspection while retaining the ordinary structural
    computation of the refined root as a separate trace. -/
public meta def relationalizeAfaikWithPhaseTrace (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM (ProofGuidedTrace afaik) :=
  relationalizeAfaikInspectionWithTrace afaik baseConfig observations

/-- A proof-guided inspection whose structural value is justified by
    computation or by a retained, kernel-checked equality. The private
    constructor prevents a caller from pairing a run with unrelated evidence. -/
public meta structure CheckedKnownValueInspection (knowledge : Iykyk.Afaik) where
  private mk ::
  run : ProofGuidedTrace knowledge
  source : CheckedValueSource knowledge run.computedTerm

/-- Inspect a proof-known value and retain the checked connection between the
    selected root and the value used by the structural computation phase. -/
public meta def inspectKnownValue (knowledge : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM (CheckedKnownValueInspection knowledge) := do
  let run ← relationalizeAfaikWithPhaseTrace knowledge baseConfig observations
  let source ← CheckedValueSource.check knowledge run.computedTerm
  return .mk run source

/-- Translate context knowledge while retaining the exact origin of every
    tuple as well as the evidence consumed by Lean selectors. -/
public meta def relationalizeAfaikWithTrace (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM (TracedDataInstance × Provenance × Expr × InspectedValue ×
      SelectorEvidence) :=
  do
    let result ← relationalizeAfaikWithPhaseTrace afaik baseConfig observations
    return (result.trace, result.provenance, result.datum, result.inspection, result.evidence)

/-- The established trace API is the checked two-phase run with its internal
    computation snapshot erased. -/
theorem relationalizeAfaikWithTrace_eq_phase_erasure (afaik : Iykyk.Afaik)
    (cfg : WalkConfig := {}) (observations : Array Expr := #[]) :
    relationalizeAfaikWithTrace afaik cfg observations = do
      let result ← relationalizeAfaikWithPhaseTrace afaik cfg observations
      return (result.trace, result.provenance, result.datum, result.inspection,
        result.evidence) := by
  rfl

/-- Compatibility projection that erases per-tuple origins. -/
public meta def relationalizeAfaikWithEvidence (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM (JsonDataInstance × Provenance × Expr × InspectedValue × SelectorEvidence) := do
  let (trace, provenance, datum, inspection, evidence) ←
    relationalizeAfaikWithTrace afaik baseConfig observations
  return (trace.data, provenance, datum, inspection, evidence)

/-- The established proof-context evidence API is exactly the traced producer
    followed by tuple-origin erasure. -/
theorem relationalizeAfaikWithEvidence_eq_trace_erasure (afaik : Iykyk.Afaik)
    (cfg : WalkConfig := {}) (observations : Array Expr := #[]) :
    relationalizeAfaikWithEvidence afaik cfg observations = do
      let (trace, provenance, datum, inspection, evidence) ←
        relationalizeAfaikWithTrace afaik cfg observations
      return (trace.data, provenance, datum, inspection, evidence) := by
  rfl

/-- Translate context knowledge, preserving the original data/provenance API. -/
public meta def relationalizeAfaikWithProvenance (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM (JsonDataInstance × Provenance × Expr) := do
  let (data, prov, datum, _, _) ← relationalizeAfaikWithEvidence afaik baseConfig observations
  return (data, prov, datum)

/-- `relationalizeAfaikWithProvenance`, data only. -/
public meta def relationalizeAfaik (afaik : Iykyk.Afaik)
    (baseConfig : WalkConfig := {}) (observations : Array Expr := #[]) :
    MetaM JsonDataInstance := do
  let (data, _, _, _, _) ← relationalizeAfaikWithEvidence afaik baseConfig observations
  return data

/-- The data-only proof-context API is the evidence-producing translation
    followed by erasure. Kept here so its proof can unfold the private worker
    without exposing the worker's implementation details. -/
theorem relationalizeAfaik_eq_evidence_erasure (afaik : Iykyk.Afaik)
    (cfg : WalkConfig := {}) (observations : Array Expr := #[]) :
    relationalizeAfaik afaik cfg observations = do
      let (data, _, _, _, _) ← relationalizeAfaikWithEvidence afaik cfg observations
      return data := by
  rfl

/-- The status Spytial needs in addition to a successful relational payload. -/
public meta structure ContextViewStatus where
  truncated : Bool := false
  inconsistent : Bool := false
  deriving Inhabited

/-- One successful IYKYK extraction together with Spytial's observation of it. -/
public meta structure ContextView where
  afaik : Iykyk.Afaik
  /-- The evidence-bearing instance produced before JSON erasure. -/
  trace : TracedDataInstance
  data : JsonDataInstance
  /-- The subterm behind each atom, for raw Lean selectors. -/
  prov : Provenance
  /-- The value a raw Lean selector's `Spytial.Sel` form receives: the root
      with its known refinements substituted. -/
  datum : Expr
  inspection : InspectedValue
  /-- Terms and certified evidence interpreting the atoms in `data`. -/
  evidence : SelectorEvidence
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
  let candidates ← afaik.facts.mapM fun fact => do
    contextualTerms cfg root (← displayedProposition fact)
  let mut stale : Array Bool := #[]
  for index in [:afaik.facts.size] do
    let proposition ← displayedProposition afaik.facts[index]!
    let isRefinement := (← refinementOf? proposition).isSome
    let isStale ← if isRefinement then pure false else
      observesAlternateRecursiveValue cfg representedTerms representedTypes proposition
    stale := stale.push isStale
  let mut selected : Std.HashSet Nat := {}
  let mut changed := true
  while changed do
    changed := false
    for index in [:afaik.facts.size] do
      if selected.contains index || stale[index]! then continue
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
      let result ←
        relationalizeAfaikInspectionWithTrace afaik walkConfig observations (some subject)
      let trace := result.trace
      let prov := result.provenance
      let datum := result.datum
      let evidence := result.evidence
      let data := trace.data
      let inspection := { result.inspection with term := (← ppExpr subject).pretty }
      return ({ truncated := afaik.truncated },
        some { afaik, trace, data, prov, datum, inspection, evidence })

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

/-- Extend the inspected expression's normal Spytial scope (`base`) with the
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

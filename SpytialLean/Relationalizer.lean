module

public import Lean
public meta import SpytialLean.Types
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Identity

namespace SpytialLean

open Lean Meta

/-! # The relationalizer

Walks an elaborated expression into atoms and relations: give every subterm a
fresh atom, then merge occurrences with the same identity — declared per type
by `SpytialIdentity`, the atom table keyed on `(type, identity)` under
confirmed structural equality, never bare `Expr.hash`. No instance ⇒ the
walker derives one; `asWritten` declines. The `Raw`/`Viewed` wrappers shift the
ambient mode for their subtree, recognized on the *pre-whnf* type head because
`Meta.whnf` melts the semireducible wrappers. Observations are also recognized
pre-whnf: their source-level computation slice becomes function-graph
relations instead of implementation-level constructor structure.
`referenceRelationalize` is a literal two-pass implementation (fresh atoms,
then merge); the fused `walkExpr` is
differentially tested against it. The two agree on the partition; when an
identity is coarser than structural, the drawn representative may differ —
the fused walker draws the first-walked occurrence. -/

/-- How subterms of a type decide identity, resolved once per type per walk
    from its `SpytialIdentity` instance (see `resolveRoute`). -/
public meta inductive IdentityRoute where
  /-- No merging: every occurrence a fresh atom (node-local; children still
      consult their own types in `declared` mode). Reached by declaring
      `asWritten`, or when nothing could be derived. -/
  | noInstance
  /-- The derived structural instance (verified: the instance that resolved
      is the registered twin's): keys are computed meta-side during the walk,
      eval only on a miss. -/
  | structural
  /-- A non-derived classifier `.identity f`: one evaluation of `f e` per
      closed subterm, memoized per subterm. -/
  | classifier (f : Expr)
  /-- A decider `.eqv r` (or an instance whose presentation `whnf` cannot
      expose, wrapped in `IdentityVia.toEqv`): one compiled comparison per
      existing group of the type. -/
  | eqvRel (r : Expr)
  deriving Inhabited

/-- Atom id → the (post-whnf) subterm that minted it. Populated for ordinary
    value atoms only: holes, hypotheses, and custom-relationalizer atoms have no
    subterm a Lean predicate could be applied to, and are absent. -/
public meta abbrev Provenance := Std.HashMap String Expr

/-- State maintained while walking an expression tree. -/
public meta structure WalkState where
  atoms : Array JsonAtom := #[]
  /-- Map from relation name to accumulated tuples. -/
  relations : Std.HashMap String (Array String × Array JsonTuple) := {}
  nextId : Nat := 0
  /-- Hole atoms, one per metavariable: occurrences of one `?m` are one hole
      under every mode — substitution structure, not identity policy. -/
  mvarAtoms : Std.HashMap MVarId String := {}
  /-- Hypothesis atoms, one per free variable, ditto. -/
  fvarAtoms : Std.HashMap FVarId String := {}
  /-- Exact named applications already emitted as function-graph points. This
      makes the result of `f x` in one graph tuple the same atom as the input
      `f x` in a later tuple. It is semantic sharing of one written term, not
      value identity. -/
  applicationAtoms : ExprStructMap String := {}
  /-- Context-only references to open constructor terms. This is separate
      from closed-value identity and never merges different symbolic terms. -/
  symbolicAtoms : ExprStructMap String := {}
  /-- Counter for short display names of determined but otherwise unnamed
      application results (`•₁`, `•₂`, ...). -/
  nextApplicationLabel : Nat := 0
  /-- Refinements currently being expanded — the cycle guard for mutual
      equations (`h₁ : x = y`, `h₂ : y = x`): a variable re-entered during its
      own refinement renders as the opaque leaf instead. -/
  refining : Std.HashSet FVarId := {}
  /-- Memo-reconcile for custom relationalizers: a repeated occurrence resolves
      to the id the relationalizer actually returned, never the discarded
      pre-allocated one. Confirmed equality, not bare hash. -/
  customSeen : ExprStructMap String := {}
  /-- Identity route per whnf'd type: `synthInstance?` runs once per type per
      walk. -/
  routeCache : ExprStructMap IdentityRoute := {}
  /-- Meta-side structural keys per whnf'd subterm (`none` = not computable:
      stuck non-literal, open child, or a dependency only evaluation could
      key). -/
  metaKeyCache : ExprStructMap (Option IdentityKey) := {}
  /-- `.identity f` results per closed subterm; failures are memoized too. -/
  evalKeyCache : ExprStructMap (Option IdentityKey) := {}
  /-- The atom table: `(type, identity) → atom id`. -/
  identityAtoms : Std.HashMap (ExprStructEq × IdentityKey) String := {}
  /-- `.eqv` group representatives per type: each new closed subterm costs one
      compiled comparison per existing group. -/
  eqvGroups : ExprStructMap (Array (Expr × String)) := {}
  /-- Exact-occurrence shortcut for `.eqv` types: a structurally identical
      subterm rejoins its group without re-evaluating the relation. -/
  eqvSeen : ExprStructMap String := {}
  /-- What each atom was walked from, for raw Lean selectors. -/
  provenance : Provenance := {}
  /-- One usable Lean term for each represented atom. Unlike selector
      provenance, this includes symbolic holes and custom-relationalizer roots:
      observations may be applied to those terms even though raw selectors must
      not resolve against them. The first term for a merged atom is retained. -/
  observationTerms : Array (Expr × String) := #[]
  /-- `r w w` per closed subterm on the `.eqv` route — see `identityVerdict`. -/
  eqvRefl : ExprStructMap Bool := {}
  /-- Per-walk cache: whnf'd type → its `Repr` instance for leaf labels;
      `none` records that the type declares none. -/
  reprInstCache : ExprStructMap (Option Expr) := {}

/-- Generate a fresh atom ID. -/
public meta def WalkState.freshId (s : WalkState) : String × WalkState :=
  let id := s!"atom_{s.nextId}"
  (id, { s with nextId := s.nextId + 1 })

private meta def subscriptDigit : Char → String
  | '0' => "₀"
  | '1' => "₁"
  | '2' => "₂"
  | '3' => "₃"
  | '4' => "₄"
  | '5' => "₅"
  | '6' => "₆"
  | '7' => "₇"
  | '8' => "₈"
  | '9' => "₉"
  | c => c.toString

/-- A visibly generated display name, distinct from both a program identifier
    and the `?u` notation used for an unknown existential witness. -/
private meta def applicationLabel (index : Nat) : String :=
  "•" ++ String.join ((toString (index + 1)).toList.map subscriptDigit)

/-- Allocate the next generated `•ₙ` display name. Every generated label in a
    walk draws from this one counter, so two distinct atoms never share one. -/
public meta def WalkState.freshApplicationLabel (s : WalkState) : String × WalkState :=
  (applicationLabel s.nextApplicationLabel,
    { s with nextApplicationLabel := s.nextApplicationLabel + 1 })

/-- Register an atom in the state. -/
public meta def WalkState.addAtom (s : WalkState) (atom : JsonAtom) : WalkState :=
  { s with atoms := s.atoms.push atom }

/-- Remember a term that an active-domain observation can apply to. Identity
    merging can send several terms to one atom; its first representative is
    enough, and matches the representative whose structure was drawn. -/
private meta def rememberObservationTerm (enabled : Bool) (term : Expr) (atomId : String) :
    StateT WalkState MetaM Unit :=
  if enabled then
    modify fun state =>
      if state.observationTerms.any fun (_, seenId) => seenId == atomId then state
      else { state with observationTerms := state.observationTerms.push (term, atomId) }
  else pure ()

/-- Add a tuple to a relation, creating the relation if needed. -/
public meta def WalkState.addTuple (s : WalkState) (relName : String) (types : Array String)
    (tuple : JsonTuple) : WalkState :=
  let existing := s.relations.getD relName (types, #[])
  { s with relations := s.relations.insert relName (existing.1, existing.2.push tuple) }

/-- Register a relation with no tuples, so an empty extension still appears. -/
public meta def WalkState.addRelation (s : WalkState) (relName : String)
    (types : Array String) : WalkState :=
  if s.relations.contains relName then s
  else { s with relations := s.relations.insert relName (types, #[]) }

/-- Convert accumulated state to ordinary extracted data. -/
public meta def WalkState.toDataInstance (s : WalkState) : JsonDataInstance :=
  let relations := s.relations.toArray.map fun (name, types, tuples) =>
    { id := name, name := name, types := types, tuples := tuples : JsonRelation }
  { atoms := s.atoms, relations := relations }

/-- Configuration for the expression walker. -/
public meta structure WalkConfig where
  /-- When true, skip Prop-typed fields (data mode). When false, show them (proof mode). -/
  filterProofs : Bool := true
  /-- Show a named application `f x` as the graph point `f[x, f x]`.
      Context knowledge enables this so repeated symbolic applications form a
      connected relational value. Ordinary value relationalization leaves it
      disabled. -/
  functionGraphs : Bool := false
  /-- Requested applications from an `observing` clause. Their function heads
      parameterize expression walking: a named application that contains one
      of these observed heads is represented by its source-level function
      graph before WHNF can replace it with implementation-level constructors. -/
  observations : Array Expr := #[]
  /-- Retain represented terms even without observations, for contextual
      relevance selection. Does not add any atoms or relations. -/
  recordTerms : Bool := false
  /-- Context mode shares exact open constructor terms (including local let
      aliases). Ordinary walks and `Raw` occurrence semantics are unchanged. -/
  shareSymbolicValues : Bool := false
  /-- Largest domain product a function tabulates into; over it, the function
      stays a leaf. -/
  maxTableTuples : Nat := 512
  /-- Equational refinements: a hypothesis variable in this map draws the term
      it is known equal to (`h : x = t` in a proof state) instead of an opaque
      leaf. Consulted at the `fvar` hole and memoized in `fvarAtoms`, so every
      occurrence shares the refined structure. -/
  refinements : Std.HashMap FVarId Expr := {}

/-- The ambient walk mode. Identity is per-type and declared; the mode is
    per-subtree — it decides only whether declarations are consulted at all. -/
public meta inductive WalkMode where
  /-- Resolve `SpytialIdentity τ` for each closed subterm, deriving one where
      the type declares none. The default. -/
  | declared
  /-- No instance consultation at all; every occurrence fresh. Hereditary —
      "as written" is a property of a whole term — until a `Viewed` shifts
      back. -/
  | asWritten
  deriving BEq, Repr, Inhabited

/-- Per-subtree walk context: threaded as an argument, so subtree scoping of
    the mode and the pop-on-exit of the unfold guard hold by construction. -/
public meta structure WalkCtx where
  mode : WalkMode := .declared
  /-- The unfold guard: ancestor subterms (post-whnf) with their atom ids —
      push-on-entry, pop-on-exit — so runaway whnf unfolding of recursive
      definitions terminates as an explicit cycle edge. Confirmed structural
      equality only, never bare hash. -/
  ancestors : Array (Expr × String) := #[]

/-- Whether an argument is erased at runtime — a proof or a type. -/
public meta def isProofArg (e : Expr) : MetaM Bool := do
  isProofLikeType (← inferType e)

/-- A custom relationalizer function.
    Receives the expression to decompose and the default walker for recursion. -/
@[expose] public meta def CustomRelationalizer :=
  Expr → (Expr → StateT WalkState MetaM String) → StateT WalkState MetaM String

/-- Maps a type name to the name of the `CustomRelationalizer` def registered for it.
    An env extension is serialized into the `.olean`, so registrations made in one
    module are visible wherever it is imported; storing the def's *name* rather than
    its value is what keeps the entries serializable. -/
public meta initialize spytialRelationalizerExt :
    SimplePersistentEnvExtension (Name × Name) (Std.HashMap Name Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (t, d) => m.insert t d
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (t, d) => m.insert t d) m) {}
  }

/-- The name of the `CustomRelationalizer` def registered for `typeName`, if any. -/
public meta def getSpytialRelationalizerName? (env : Environment) (typeName : Name) : Option Name :=
  spytialRelationalizerExt.getState env |>.get? typeName

/-- Register `declName` (which must have type `CustomRelationalizer`) as the
    relationalizer for `typeName`. -/
public meta def setSpytialRelationalizer (typeName declName : Name) : CoreM Unit :=
  modifyEnv fun env => spytialRelationalizerExt.addEntry env (typeName, declName)

/-- Session-local memo of compiled relationalizers, keyed by def name + body
    hash so an interactive body edit recompiles instead of serving the stale
    closure. -/
public meta initialize spytialRelationalizerCache :
    IO.Ref (Std.HashMap Name (UInt64 × CustomRelationalizer)) ← IO.mkRef {}

/-- Compile (with memoization) the custom relationalizer registered for `typeName`. -/
public meta unsafe def getSpytialRelationalizerImpl (typeName : Name) :
    MetaM (Option CustomRelationalizer) := do
  let some declName := getSpytialRelationalizerName? (← getEnv) typeName | return none
  -- `value? = none` (opaque, `partial` fixpoint wrappers) falls back to hash 0:
  -- name-only caching, no edit detection
  let bodyHash := ((← getConstInfo declName).value?.map Expr.hash).getD 0
  if let some (h, fn) := (← spytialRelationalizerCache.get).get? declName then
    if h == bodyHash then return some fn
  let fn ← Meta.evalExpr CustomRelationalizer (mkConst ``CustomRelationalizer) (mkConst declName)
  spytialRelationalizerCache.modify (·.insert declName (bodyHash, fn))
  return some fn

/-- Look up the custom relationalizer registered for a type name, if any. Reads the
    persistent name registry, then evaluates the named def (memoized per process). -/
@[implemented_by getSpytialRelationalizerImpl]
public meta opaque getSpytialRelationalizer? (typeName : Name) : MetaM (Option CustomRelationalizer)

/-! ## Identity resolution

Three ways a type's identity is computed, per its instance: a derived type's
generated meta twin computes it meta-side (no `evalExpr`; a miss falls back
to one evaluation of the compiled classifier); a non-derived classifier costs
one evaluation per closed subterm; a decider costs one compiled comparison
per existing group. Open subterms have no value, hence no identity: fresh
atoms, node-local. -/

/-- Open subterms have no value, hence no identity — they stay as written. -/
public meta def isClosedValue (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && !e.hasLevelParam && !e.hasSorry

/-- Shift the ambient mode for `Raw`/`Viewed` wrappers spelled in `ty`.
    `whnfR` sees through reducible abbreviations but not the semireducible
    wrappers themselves; peeling recurses so the innermost wrapper wins
    (`Raw (Viewed τ)` walks `declared`). -/
private meta partial def shiftForWrappers (mode : WalkMode) (ty : Expr) : MetaM WalkMode := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``Raw 1 then
    shiftForWrappers .asWritten ty.appArg!
  else if ty.isAppOfArity ``Viewed 1 then
    shiftForWrappers .declared ty.appArg!
  else
    return mode

private meta unsafe def evalIdentityKeyUnsafe (e : Expr) : MetaM IdentityKey :=
  Meta.evalExpr IdentityKey (mkConst ``IdentityKey) e

@[implemented_by evalIdentityKeyUnsafe]
private meta opaque evalIdentityKeyOpaque (e : Expr) : MetaM IdentityKey

/-- Evaluate a (closed) `IdentityKey`-valued expression; `none` on any
    compilation/evaluation failure — the caller falls back to a fresh atom
    without disturbing other groups. -/
private meta def evalIdentityKey? (e : Expr) : MetaM (Option IdentityKey) := do
  try return some (← evalIdentityKeyOpaque e) catch _ => return none

private meta unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool :=
  Meta.evalExpr Bool (mkConst ``Bool) e

@[implemented_by evalBoolUnsafe]
private meta opaque evalBoolOpaque (e : Expr) : MetaM Bool

private meta def evalBool? (e : Expr) : MetaM (Option Bool) := do
  try return some (← evalBoolOpaque e) catch _ => return none

-- TODO(norm?-display): drawing `n e`'s structure per new group needs value →
-- `Expr` reification (a `ToExpr` for arbitrary user types), which doesn't
-- generally exist. Merging is unaffected, by `identity (norm x) = identity x`.

/-- Read a resolved instance's presentation: expose it with `whnf`, and take
    the structural route only when the instance that resolved *is* the derived
    one (checked against the registered twin's parent name, so an instance
    shadowing a derived one routes as an ordinary classifier — meta and eval
    then agree by construction). -/
private meta def routeOfInstance (tyKey inst : Expr) : MetaM IdentityRoute := do
  let viaW ← whnf (← mkAppOptM ``SpytialIdentity.via #[some tyKey, some inst])
  if viaW.isAppOfArity ``IdentityVia.asWritten 1 then
    return .noInstance
  if viaW.isAppOfArity ``IdentityVia.identity 2 then
    let env ← getEnv
    let structural := match tyKey.getAppFn, inst.getAppFn.constName? with
      | .const h _, some instName =>
        match structuralTwinName? env h with
        | some twin => twin.getPrefix == instName
        | none => false
      | _, _ => false
    return (if structural then .structural else .classifier viaW.appArg!)
  if viaW.isAppOfArity ``IdentityVia.eqv 2 then
    return .eqvRel viaW.appArg!
  -- presentation opaque to whnf (a non-`@[expose]` instance body). `toEqv` is
  -- total and correct for the merging arms, at group-comparison cost — but the
  -- `.eqvRel` route memoizes per expression, so an `asWritten` reached this way
  -- would merge on the memo alone. Ask the compiled code first.
  if (← evalBool? (← mkAppM ``IdentityVia.isAsWritten #[viaW])) == some true then
    return .noInstance
  return .eqvRel (← mkAppM ``IdentityVia.toEqv #[viaW])

/-- Resolve how subterms of (whnf'd, closed) type `tyKey` decide identity:
    declared instance, else `ToIdentityKey` encoding, else structural identity
    derived on demand — the same order, for the same reason, as `depPath`.
    Memoized per type, so the derivation attempt and the decline warning happen
    once per walk. -/
private meta def resolveRoute (tyKey : Expr) : StateT WalkState MetaM IdentityRoute := do
  if let some r := (← get).routeCache[(⟨tyKey⟩ : ExprStructEq)]? then
    return r
  let r ← do
    try
      if let some inst ← synthInstance? (← mkAppM ``SpytialIdentity #[tyKey]) then
        routeOfInstance tyKey inst
      else if !(spytial.identity.auto.get (← getOptions)) then
        pure .noInstance
      else if let some enc ← synthInstance? (← mkAppM ``ToIdentityKey #[tyKey]) then
        pure (.classifier (← mkAppOptM ``ToIdentityKey.toKey #[some tyKey, some enc]))
      else
        match ← deriveIdentity tyKey with
        | .derived =>
          match ← synthInstance? (← mkAppM ``SpytialIdentity #[tyKey]) with
          | some inst => routeOfInstance tyKey inst
          | none =>
            let missing ← tyKey.getAppArgs.filterM fun a => do
              if ← isIdentityCandidate a then
                return (← synthInstance? (← mkAppM ``SpytialIdentity #[a])).isNone
              return false
            let blame :=
              if missing.isEmpty then m!"it still does not synthesize"
              else m!"'{missing[0]!}' has no `SpytialIdentity`"
            logWarning m!"'{tyKey}' was derived but {blame}. \
              Equal subterms draw as separate atoms."
            pure .noInstance
        | .refused why =>
          let applied := if tyKey.getAppNumArgs == 0 then m!"{tyKey}" else m!"({tyKey})"
          logWarning m!"'{tyKey}' has no `SpytialIdentity` and none can be derived: \
            {why}\nEqual subterms draw as separate atoms. Declare \
            `instance : SpytialIdentity {applied} := .asWritten` to accept that."
          pure .noInstance
        | .notApplicable => pure .noInstance
    catch _ => pure .noInstance
  modify fun s => { s with routeCache := s.routeCache.insert ⟨tyKey⟩ r }
  return r

/-! ## Meta-side keys for derived structural instances

For a derived type the walker runs the generated meta twin — emitted by the
deriving handler from the same plan as the compiled classifier, so the two
cannot drift. Any meta miss (a field whose instance is a user classifier or
decider, an encoding without a usable `MetaEncode` twin, a stuck value) falls
back to evaluating the compiled classifier: identical keys at evaluation
cost, so meta- and eval-computed keys share one atom table. The fallback
declines subterms containing `@[irreducible]`/`opaque` constants — there the
two computers would disagree (spelling vs unfolded value), so those stay
fresh. -/

private meta unsafe def evalOptionKeyUnsafe (e : Expr) : MetaM (Option IdentityKey) :=
  Meta.evalExpr (Option IdentityKey)
    (mkApp (mkConst ``Option [Level.zero]) (mkConst ``IdentityKey)) e

@[implemented_by evalOptionKeyUnsafe]
private meta opaque evalOptionKeyOpaque (e : Expr) : MetaM (Option IdentityKey)

/-- Evaluate a closed `Option IdentityKey`-valued expression; `none` on any
    compilation/evaluation failure. -/
private meta def evalOptionKey? (e : Expr) : MetaM (Option IdentityKey) := do
  try evalOptionKeyOpaque e catch _ => return none

/-- The type of a generated meta twin (see `Identity.lean`'s deriving
    handler): the walker's dispatch for child keys, then the value. -/
@[expose] public meta def StructuralTwin :=
  (Expr → MetaM (Option IdentityKey)) → Expr → MetaM (Option IdentityKey)

/-- Session-local memo of compiled twins, keyed by def name + body hash so an
    interactive edit recompiles instead of serving the stale closure. -/
public meta initialize spytialTwinCache :
    IO.Ref (Std.HashMap Name (UInt64 × StructuralTwin)) ← IO.mkRef {}

/-- Compile (with memoization) the meta twin registered for `typeName`. -/
public meta unsafe def getStructuralTwinImpl (typeName : Name) :
    MetaM (Option StructuralTwin) := do
  let some declName := structuralTwinName? (← getEnv) typeName | return none
  -- a registered twin that doesn't resolve (private-module codegen edge)
  -- degrades to the eval fallback rather than failing the walk
  let some info := (← getEnv).find? declName | return none
  let bodyHash := (info.value?.map Expr.hash).getD 0
  if let some (h, fn) := (← spytialTwinCache.get).get? declName then
    if h == bodyHash then return some fn
  let fn ← Meta.evalExpr StructuralTwin (mkConst ``StructuralTwin) (mkConst declName)
  spytialTwinCache.modify (·.insert declName (bodyHash, fn))
  return some fn

/-- The compiled meta twin registered for a type name, if any. -/
@[implemented_by getStructuralTwinImpl]
public meta opaque getStructuralTwin? (typeName : Name) : MetaM (Option StructuralTwin)

/-- The derived structural key of `e`: run the type's generated meta twin —
    born from the same plan as the compiled classifier, so keys agree —
    dispatching child keys back through this walk, for central memoization
    and one twin load per type. `none` when no twin loads or a child no route
    can key: the caller falls back to the compiled classifier. Memoized per
    (whnf'd) subterm. -/
public meta partial def structuralKey? (e : Expr) : StateT WalkState MetaM (Option IdentityKey) := do
  let cacheRef ← IO.mkRef (← get).metaKeyCache
  let rec core (a : Expr) : MetaM (Option IdentityKey) := do
    if !isClosedValue a then return none
    let w ← whnf a
    if let some r := (← cacheRef.get)[(⟨w⟩ : ExprStructEq)]? then
      return r
    let r ← do
      let ty ← whnf (← inferType w)
      match ty.getAppFn with
      | .const h _ =>
        match ← getStructuralTwin? h with
        | some twin => twin core w
        | none => pure none
      | _ => pure none
    cacheRef.modify (·.insert ⟨w⟩ r)
    return r
  let r ← core e
  let cache ← cacheRef.get
  modify fun s => { s with metaKeyCache := cache }
  return r

/-! ## The identity decision -/

/-- Whether `e` mentions a constant the opacity discipline refuses to unfold.
    Evaluation would pierce the barrier, so the eval fallback declines and the
    subterm stays fresh — the safe direction. -/
private meta def hasOpaqueBarrier (e : Expr) : MetaM Bool := do
  let env ← getEnv
  for c in e.getUsedConstants do
    if ← isIrreducible c then return true
    if env.find? c matches some (.opaqueInfo _) then return true
  return false

private meta inductive IdVerdict where
  /-- Merged into an existing atom: reuse its id, do not walk children. -/
  | reuse (id : String)
  /-- First occurrence of a keyed identity: allocate, then `registerIdentity`. -/
  | keyed (tyKey : Expr) (k : IdentityKey)
  /-- First member of a new `.eqv` group: allocate, then `registerIdentity`. -/
  | grouped (tyKey : Expr)
  /-- No identity participation: fresh atom. -/
  | fresh

/-- Normalize local aliases and natural-literal encodings for contextual
    references, without unfolding observation functions. IYKYK's simplifier
    can turn a raw literal into `OfNat.ofNat`; reduction checks the actual
    instance rather than assuming that every `OfNat Nat n` denotes `n`. -/
public meta def normalizeReferenceTerm (e : Expr) : MetaM Expr := do
  transform (← zetaReduce e) (pre := fun term => do
    if let .mdata _ body := term then return .visit body
    if term.isAppOfArity ``OfNat.ofNat 3 && term.getAppArgs[0]!.isConstOf ``Nat then
      return .done (← whnf term)
    return .continue)

/-- Exact open terms necessarily have equal classifier keys. Decider-based
    identities may be non-reflexive (for example, over an `asWritten` field),
    so they cannot use this shortcut without evaluating the open term. -/
private meta def symbolicValueKey? (cfg : WalkConfig) (mode : WalkMode) (e tyKey : Expr) :
    StateT WalkState MetaM (Option Expr) := do
  unless cfg.shareSymbolicValues && mode == .declared && (e.hasFVar || e.hasMVar) do return none
  -- Do not synthesize identities by solving unknown type parameters.
  if tyKey.hasFVar || tyKey.hasMVar then return none
  let .const name _ := e.getAppFn | return none
  let some (.ctorInfo _) := (← getEnv).find? name | return none
  match ← resolveRoute tyKey with
  | .structural | .classifier _ => return some (← normalizeReferenceTerm e)
  | .noInstance | .eqvRel _ => return none

/-- Decide how a closed, `declared`-mode subterm participates in identity.
    Pure lookup/eval + memoization; allocation and registration are the
    caller's (so the fused walker and the reference merge pass share exactly
    this decision procedure). -/
private meta def identityVerdict (tyKey e : Expr) : StateT WalkState MetaM IdVerdict := do
  match ← resolveRoute tyKey with
  | .noInstance => return .fresh
  | .structural =>
    let k? ← do
      match ← structuralKey? e with
      | some k => pure (some k)
      | none =>
        -- meta miss: evaluate the compiled classifier instead — identical
        -- keys (the plan and the code share one source), one evaluation,
        -- memoized. Except under a deliberate barrier: evaluation would
        -- unfold the `@[irreducible]`/`opaque` heads the meta side keys by
        -- spelling, so barrier-containing subterms stay fresh instead.
        if isClosedValue e && !(← hasOpaqueBarrier e) then
          let w ← whnf e
          match (← get).evalKeyCache[(⟨w⟩ : ExprStructEq)]? with
          | some r => pure r
          | none =>
            let r ← try
                evalOptionKey? (← mkAppM ``SpytialIdentity.runtimeKey? #[w])
              catch _ => pure none
            modify fun s => { s with evalKeyCache := s.evalKeyCache.insert ⟨w⟩ r }
            pure r
        else pure none
    match k? with
    | some k =>
      if let some id := (← get).identityAtoms[((⟨tyKey⟩ : ExprStructEq), k)]? then
        return .reuse id
      return .keyed tyKey k
    | none => return .fresh
  | .classifier f =>
    let w ← whnf e
    let k? ← do
      match (← get).evalKeyCache[(⟨w⟩ : ExprStructEq)]? with
      | some r => pure r
      | none =>
        let r ← evalIdentityKey? (mkApp f w)
        modify fun s => { s with evalKeyCache := s.evalKeyCache.insert ⟨w⟩ r }
        pure r
    match k? with
    | some k =>
      if let some id := (← get).identityAtoms[((⟨tyKey⟩ : ExprStructEq), k)]? then
        return .reuse id
      return .keyed tyKey k
    | none => return .fresh
  | .eqvRel r =>
    let w ← whnf e
    -- `eqvSeen` and the group scan both assume the decider is reflexive. A
    -- derived instance over an `asWritten` field is not: the type as a whole
    -- still has merging arms, so it cannot present `.asWritten`, but `w`
    -- itself must not merge — with an identical spelling least of all. Only an
    -- evaluation that answers `false` establishes that; an evaluation failure
    -- keeps the exact-spelling merge, which needs no evaluation.
    let refl ← do
      match (← get).eqvRefl[(⟨w⟩ : ExprStructEq)]? with
      | some b => pure b
      | none =>
        let b := (← evalBool? (mkApp2 r w w)) != some false
        modify fun s => { s with eqvRefl := s.eqvRefl.insert ⟨w⟩ b }
        pure b
    unless refl do return .fresh
    if let some id := (← get).eqvSeen[(⟨w⟩ : ExprStructEq)]? then
      return .reuse id
    for (rep, gid) in (← get).eqvGroups[(⟨tyKey⟩ : ExprStructEq)]?.getD #[] do
      match ← evalBool? (mkApp2 r rep w) with
      | some true =>
        modify fun s => { s with eqvSeen := s.eqvSeen.insert ⟨w⟩ gid }
        return .reuse gid
      | some false => pure ()
      | none =>
        -- eval failure ⇒ fresh atom, representative pool untouched
        return .fresh
    return .grouped tyKey

/-- Record the verdict's registration for a newly allocated atom. -/
private meta def registerIdentity (v : IdVerdict) (e : Expr) (atomId : String) :
    StateT WalkState MetaM Unit := do
  match v with
  | .keyed tyKey k =>
    modify fun s =>
      { s with identityAtoms := s.identityAtoms.insert (⟨tyKey⟩, k) atomId }
  | .grouped tyKey => do
    let w ← whnf e
    modify fun s =>
      { s with
        eqvGroups := s.eqvGroups.insert ⟨tyKey⟩
          ((s.eqvGroups[(⟨tyKey⟩ : ExprStructEq)]?.getD #[]).push (w, atomId))
        eqvSeen := s.eqvSeen.insert ⟨w⟩ atomId }
  | _ => pure ()

/-! ## The walk -/

/-- Hole handling, shared by the fused walker and the reference: an unassigned
    metavariable or an opaque hypothesis has no structure to decompose, so it
    renders as a leaf that keeps its structural atom type (a `Tree`-shaped
    hole still occupies a `Tree` slot, so `Tree` specs apply). One atom per
    metavariable/hypothesis, under every mode. Must short-circuit *before*
    custom-relationalizer dispatch — a value decomposer must never be handed a
    bare hole of its target type. A variable with an entry in
    `cfg.refinements` is not opaque: it draws the shape IYKYK established. -/
private meta def holeAtom? (cfg : WalkConfig) (recurse : Expr → StateT WalkState MetaM String)
    (e ty : Expr) : StateT WalkState MetaM (Option String) := do
  match e with
  | .mvar mvarId =>
    if let some id := (← get).mvarAtoms[mvarId]? then return some id
    let typeName ← sigOfType ty
    let userName := (← mvarId.getDecl).userName
    let s ← get
    let (atomId, s) := s.freshId
    set (s.addAtom { id := atomId, type := typeName, label := holeLabel userName })
    modify fun s => { s with mvarAtoms := s.mvarAtoms.insert mvarId atomId }
    return some atomId
  | .fvar fvarId =>
    if let some id := (← get).fvarAtoms[fvarId]? then return some id
    -- An equational refinement draws the term the variable is known equal to;
    -- the memo below makes every occurrence share the refined structure. A
    -- cyclic chain re-entering the variable falls through to the opaque leaf.
    if let some rhs := cfg.refinements[fvarId]? then
      if !(← get).refining.contains fvarId then
        modify fun s => { s with refining := s.refining.insert fvarId }
        let id ← recurse rhs
        modify fun s => { s with refining := s.refining.erase fvarId,
                                 fvarAtoms := s.fvarAtoms.insert fvarId id }
        return some id
    let typeName ← sigOfType ty
    let userName ← fvarId.getUserName
    let s ← get
    let (atomId, s) := s.freshId
    set (s.addAtom { id := atomId, type := typeName, label := hypLabel userName })
    modify fun s => { s with fvarAtoms := s.fvarAtoms.insert fvarId atomId }
    return some atomId
  | _ => return none

/-- Custom-relationalizer dispatch, shared by both walkers: a custom
    `spytial_relationalizer` wins over any identity instance, in every mode
    (it is the decomposition layer, not identity policy). `mkRecurse` receives
    a pre-allocated guard id — pushed as an ancestor by the caller — bounding
    degenerate re-walks of `e` inside the relationalizer exactly as before;
    the memo then reconciles repeated occurrences to the id the relationalizer
    actually returned. -/
private meta def customDispatch? (eOrig e tyKey : Expr)
    (mkRecurse : String → Expr → StateT WalkState MetaM String) :
    StateT WalkState MetaM (Option String) := do
  let .const typeConstName _ := tyKey.getAppFn | return none
  let some relFn ← getSpytialRelationalizer? typeConstName | return none
  if let some id := (← get).customSeen[(⟨e⟩ : ExprStructEq)]? then
    return some id
  let s ← get
  let (guardId, s) := s.freshId
  set s
  let id ← relFn eOrig (mkRecurse guardId)
  modify fun s => { s with customSeen := s.customSeen.insert ⟨e⟩ id }
  return some id

/-- The target column's type sig: the child's own; the owner's on meta failure,
    so no value that walked before fails now. -/
private meta def columnSig (owner : String) (child : Expr) : MetaM String := do
  try
    return (← sigOfType (← inferType child))
  catch _ =>
    return owner

/-- The domain product as index tuples, lexicographic with the first binder
    outermost. -/
private meta def TabulationPlan.points (plan : TabulationPlan) : Array (Array Nat) := Id.run do
  let mut points := #[(#[] : Array Nat)]
  for b in plan.binders do
    let mut next := #[]
    for pt in points do
      for i in [:b.elems.size] do
        next := next.push (pt.push i)
    points := next
  return points

private meta def pick [Inhabited α] (columns : Array (Array α)) (pt : Array Nat) : Array α :=
  Id.run do
    let mut picked := #[]
    for col in [:pt.size] do
      picked := picked.push columns[col]![pt[col]!]!
    return picked

/-- The proposition paired with its `Decidable` instance. Synthesis reduces
    beta but not delta, so a proposition behind a definition matches no
    instance head: `a ∈ ({x | p x} : Set α)` is `setOf p a`, and nothing is
    declared about `setOf`. -/
private meta def decidableFor? (p : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some inst ← Meta.synthInstance? (← mkAppM ``Decidable #[p]) then
    return some (p, inst)
  let p ← Meta.whnf p
  return (← Meta.synthInstance? (← mkAppM ``Decidable #[p])).map ((p, ·))

/-- Decide a closed proposition: `whnf` the `Decidable` instance to a
    constructor, compiled `decide p` when that sticks. `none` is undecided,
    never a guess. -/
private meta def decideProp? (p : Expr) : MetaM (Option Bool) := do
  try
    let some (p, inst) ← decidableFor? p | return none
    match (← Meta.whnf inst).getAppFn with
    | .const ``Decidable.isTrue _ => return some true
    | .const ``Decidable.isFalse _ => return some false
    | _ => evalBool? (← mkAppOptM ``Decidable.decide #[some p, some inst])
  catch _ => return none

/-- The arguments of an application that carry data. Proofs, types, and
    typeclass instances are elaboration machinery rather than graph columns. -/
public meta def dataArgsOf (e : Expr) : MetaM (Array Expr) := do
  let mut out : Array Expr := #[]
  for a in e.getAppArgs do
    if ← isProofArg a then continue
    if (← Meta.isClass? (← inferType a)).isSome then continue
    out := out.push a
  return out

/-- Read a named application as a point in the function's graph. Constructors
    are values, not functions being observed. -/
public meta def graphSide? (side : Expr) : MetaM (Option (String × Array Expr)) := do
  let name? ← match side.getAppFn with
    | .const ``HAdd.hAdd _ => pure (some "add")
    | .const n _ =>
      match (← getEnv).find? n with
      | some (.ctorInfo _) => pure none
      | _ => pure (some (shortName n))
    | .fvar id => pure (some (hypLabel (← id.getUserName)))
    | _ => pure none
  let some name := name? | return none
  let args ← dataArgsOf side
  if args.isEmpty then return none
  return some (name, args)

/-- Whether `application` has the same function head as one of the explicitly
    requested observations. Function identity, rather than the applied root
    argument, makes `observing [height]` govern every `height _` appearing in
    context expressions. -/
private meta def hasObservedHead (cfg : WalkConfig) (application : Expr) : Bool :=
  cfg.observations.any fun observation =>
    observation.getAppFn.equal application.getAppFn

/-- Whether a source expression depends on an explicitly observed
    application. This is the computation slice whose named applications must
    be reified before reduction: `height r + 1` depends on `height`, so both
    `height` and the enclosing addition become function-graph relations. -/
public meta partial def dependsOnObservation (cfg : WalkConfig) (expression : Expr) :
    MetaM Bool := do
  if cfg.observations.isEmpty then return false
  if hasObservedHead cfg expression && (← graphSide? expression).isSome then return true
  for argument in ← dataArgsOf expression do
    if ← dependsOnObservation cfg argument then return true
  return false

/-- A named source application in the computation slice selected by
    `observing`. Such an application is a relational boundary before WHNF. -/
public meta def observedGraphSide? (cfg : WalkConfig) (expression : Expr) :
    MetaM (Option (String × Array Expr)) := do
  let some side ← graphSide? expression | return none
  unless ← dependsOnObservation cfg expression do return none
  return some side

/-- Emit a named application `f xs` as the graph point `f[xs, f xs]`.
    Repeated applications reuse the same output atom. -/
private meta def emitFunctionGraph? (cfg : WalkConfig)
    (recurse : Expr → StateT WalkState MetaM String) (e : Expr) (typeName atomId : String) :
    StateT WalkState MetaM Bool := do
  unless cfg.functionGraphs do return false
  let some (relName, args) ← graphSide? e | return false
  let label ← modifyGet WalkState.freshApplicationLabel
  modify fun state =>
    let state := state.addAtom { id := atomId, type := typeName, label }
    { state with applicationAtoms := state.applicationAtoms.insert ⟨e⟩ atomId }
  let mut ids : Array String := #[]
  let mut types : Array String := #[]
  for arg in args do
    ids := ids.push (← recurse arg)
    types := types.push (← sigOfType (← inferType arg))
  ids := ids.push atomId
  types := types.push typeName
  let tuple : JsonTuple := { atoms := ids, types }
  modify fun state => state.addTuple relName types tuple
  return true

/-- Emit `relName` as the flat table over the enumerable domain product;
    report whether it fired. A data codomain gives `(owner, d₁, …, dₖ,
    result)`; a `Prop` codomain has no result column — a tuple exactly where
    the proposition decides true. -/
private meta def tabulate? (cfg : WalkConfig) (recurse : Expr → StateT WalkState MetaM String)
    (relName ownerSig ownerId : String) (value : Expr) : StateT WalkState MetaM Bool := do
  let some plan ← tabulationPlan? (← inferType value) | return false
  unless plan.size ≤ cfg.maxTableTuples do return false
  let fn@(.lam ..) ← Meta.whnf value | return false
  let types := #[ownerSig] ++ (← plan.tailTypes.mapM (sigOfType ·))
  let columns := plan.binders.map (·.elems.map (·.2))
  let points := plan.points
  match plan.kind with
  | .data =>
    modify (·.addRelation relName types)
    let ids ← columns.mapM (·.mapM recurse)
    for pt in points do
      let resId ← recurse (← Meta.whnf (mkAppN fn (pick columns pt)))
      let atoms := #[ownerId] ++ pick ids pt ++ #[resId]
      modify fun s => s.addTuple relName types { atoms, types }
    return true
  | .prop =>
    -- decide every point before walking any atom: an undecided point bails
    -- without a trace
    let mut holds := #[]
    for pt in points do
      let some verdict ← decideProp? (mkAppN fn (pick columns pt)) | return false
      if verdict then holds := holds.push pt
    modify (·.addRelation relName types)
    -- walk only elements a true tuple names; the two-pass reference prunes
    -- orphans
    let mut ids := columns.map (·.map fun _ => (none : Option String))
    for pt in holds do
      let mut atoms := #[ownerId]
      for col in [:pt.size] do
        let i := pt[col]!
        let id ← match ids[col]![i]! with
          | some id => pure id
          | none => do
            let id ← recurse columns[col]![i]!
            ids := ids.set! col (ids[col]!.set! i (some id))
            pure id
        atoms := atoms.push id
      modify fun s => s.addTuple relName types { atoms, types }
    return true

/-! ### Instance-evaluated leaf labels

A closed leaf whose type declares `Repr` reads as its evaluated value rather
than its spelling. Labels only — a non-injective `Repr` feeding identity would
merge distinct atoms. -/

private meta unsafe def evalFormatUnsafe (e : Expr) : MetaM Std.Format :=
  Meta.evalExpr Std.Format (mkConst ``Std.Format) e

/-- Evaluate a closed `Std.Format`-valued expression (leaf labels via `Repr`). -/
@[implemented_by evalFormatUnsafe]
private meta opaque evalFormat (e : Expr) : MetaM Std.Format

/-- The `Repr` instance for the (whnf'd) type, synthesized at most once per
    walk per type. -/
private meta def getReprInst? (tyKey : Expr) : StateT WalkState MetaM (Option Expr) := do
  if let some cached := (← get).reprInstCache[(⟨tyKey⟩ : ExprStructEq)]? then
    return cached
  let inst? ← try
      synthInstance? (← mkAppM ``Repr #[tyKey])
    catch _ => pure none
  modify fun s => { s with reprInstCache := s.reprInstCache.insert ⟨tyKey⟩ inst? }
  return inst?

/-- Whether the term reaches a constant with no runtime value. Compiling one
    yields its type's default instead of failing, so `0` would be reported for
    an `opaque n : Nat` as confidently as for a real zero. `@[irreducible]` is
    not this: it has a body, and evaluating it is the point. -/
private meta def hasValuelessConst (e : Expr) : MetaM Bool := do
  let env ← getEnv
  return e.getUsedConstants.any fun n =>
    match env.find? n with
    | some (.opaqueInfo _) | some (.axiomInfo _) => true
    | _ => false

/-- Label for a leaf atom: `repr` evaluated when the term is closed and its
    type declares it, otherwise the pretty-printed expression. A failure is not
    memoized against the type -- the causes that survive the guard above
    (`extern` with no Lean body, `quot`) belong to the term, so poisoning the
    type would make an unrelated leaf's label depend on walk order. -/
private meta def leafLabel (e tyKey : Expr) : StateT WalkState MetaM String := do
  if isClosedValue e && !(← hasValuelessConst e) then
    if let some inst ← getReprInst? tyKey then
      try
        let fmt ← evalFormat (← mkAppOptM ``repr #[none, some inst, some e])
        return fmt.pretty
      catch _ =>
        pure ()
  ppLabel e

/-- Emit the atom for `e` (already whnf'd; id already allocated) and walk its
    children through `recurse` — the display dispatch shared by the fused
    walker and the two-pass reference. `recurse` closes over the child walk
    context (ambient mode, unfold-guard ancestors). -/
private meta def emitNode (cfg : WalkConfig) (recurse : Expr → StateT WalkState MetaM String)
    (e ty tyKey : Expr) (origName : Option Name) (atomId : String)
    (forceFunctionGraph : Bool := false) :
    StateT WalkState MetaM Unit := do
  if forceFunctionGraph then
    let typeName ← sigOfType ty
    unless ← emitFunctionGraph? { cfg with functionGraphs := true } recurse e typeName atomId do
      let label ← leafLabel e tyKey
      modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
    return
  match e with
  -- Nat literal
  | .lit (.natVal n) =>
    modify fun s => s.addAtom { id := atomId, type := "Nat", label := toString n }

  -- String literal
  | .lit (.strVal str) =>
    modify fun s => s.addAtom { id := atomId, type := "String", label := s!"\"{str}\"" }

  -- Lambda — tabulate over an enumerable domain, otherwise labeled node
  | .lam binderName _ _ _ => do
    let typeName ← sigOfType ty
    let label := match origName with
      | some n => shortName n
      | none => s!"λ {binderName}"
    modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
    -- no owning field here, so the function itself is column 0
    let _ ← tabulate? cfg recurse "maps" typeName atomId e

  | _ => do
    -- Try to get the type name
    let typeName ← sigOfType ty

    -- Check if it's an application of a constructor
    match e.getAppFn with
    | .const fnName _ => do
      let env ← getEnv
      -- Is it a constructor?
      if let some (.ctorInfo ci) := env.find? fnName then
        let ctorShortName := shortName fnName
        modify fun s => s.addAtom { id := atomId, type := typeName, label := ctorShortName }
        let binderNames := ctorDataBinderNames ci
        -- Process data arguments (skip type and proof parameters)
        let args := e.getAppArgs
        let dataArgs := args.extract ci.numParams args.size
        for i in [:dataArgs.size] do
          let arg := dataArgs[i]!
          let isProof ← if cfg.filterProofs then isProofArg arg else pure false
          unless isProof do
            let fieldName := fieldRelName ctorShortName binderNames i
            unless ← tabulate? cfg recurse fieldName typeName atomId arg do
              let childId ← recurse arg
              let types := #[typeName, ← columnSig typeName arg]
              let tuple := { atoms := #[atomId, childId], types := types }
              modify fun state => state.addTuple fieldName types tuple
      -- stuck match (iota can't fire on a hole/hypothesis discriminant):
      -- ternary scrutinee edges; motive and alternatives are plumbing
      else if let some minfo := getMatcherInfoCore? env fnName then
        let args := e.getAppArgs
        if args.size == minfo.arity then
          modify fun s => s.addAtom { id := atomId, type := typeName, label := "match" }
          for i in [:minfo.numDiscrs] do
            let discr := args[minfo.getFirstDiscrPos + i]!
            let isProof ← if cfg.filterProofs then isProofArg discr else pure false
            unless isProof do
              let posId ← recurse (mkRawNatLit i)
              let childId ← recurse discr
              let types := #[typeName, "Nat", ← columnSig typeName discr]
              modify fun s => s.addTuple "scrutinee" types
                { atoms := #[atomId, posId, childId], types := types }
        else
          -- partially/over-applied matcher: generic leaf
          let label ← ppLabel e
          modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
      -- Is it a structure projection?
      else if (← typeHead? ty).any (isStructure env ·) then
        -- Walk all structure fields
        let tyConst := (← typeHead? ty).getD .anonymous
        let fields := getStructureFields env tyConst
        modify fun s => s.addAtom { id := atomId, type := typeName, label := typeName }
        for fieldName in fields do
          let proj ← Meta.mkProjection e fieldName
          let isProof ← if cfg.filterProofs then isProofArg proj else pure false
          unless isProof do
            let projReduced ← Meta.whnf proj
            let fn := fieldName.toString (escape := false)
            unless ← tabulate? cfg recurse fn typeName atomId projReduced do
              let childId ← recurse projReduced
              let types := #[typeName, ← columnSig typeName projReduced]
              modify fun s => s.addTuple fn types
                { atoms := #[atomId, childId], types := types }
      else do
        unless ← emitFunctionGraph? cfg recurse e typeName atomId do
          -- Generic function application or unknown — leaf atom
          let label ← leafLabel e tyKey
          modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
    | _ => do
      unless ← emitFunctionGraph? cfg recurse e typeName atomId do
        -- Not a named application — leaf atom
        let label ← leafLabel e tyKey
        modify fun s => s.addAtom { id := atomId, type := typeName, label := label }

/-- Walk a Lean expression and produce atoms + relations.
    Returns the atom ID assigned to this expression.

    Merging: in `declared` mode, each closed subterm's type resolves
    `SpytialIdentity`; subterms with the same `(type, identity)` are one atom,
    and a repeated identity returns the existing atom without re-walking the
    subtree (the first-walked occurrence is the drawn representative). An
    `asWritten` type, a refused derivation, an open subterm, meta-key failure,
    or eval failure ⇒ a fresh atom, node-local. In `asWritten` mode no
    instance is consulted at all;
    `Raw`/`Viewed` shift the mode for their subtree. -/
public meta partial def walkExpr (cfg : WalkConfig := {}) (eOrig : Expr)
    (ctx : WalkCtx := {}) : StateT WalkState MetaM String := do
  -- Save original name before WHNF unfolds it
  let origName := eOrig.getAppFn.constName?
  -- Raw/Viewed shift the ambient mode; recognized on the pre-whnf type because
  -- whnf melts the semireducible wrappers (which is also why no wrapper atom
  -- is ever emitted). A wrapper value that is not a literal `mk` application
  -- (a hole, a hypothesis) falls through to the as-written rendering of
  -- what's there.
  let mode ← shiftForWrappers ctx.mode (← Meta.inferType eOrig)
  -- An observation is an input to relationalization, not a post-pass. Preserve
  -- the source spelling of named computations that depend on an observed
  -- application; only other expressions WHNF to expose data constructors.
  let sourceFunctionGraph := (← observedGraphSide? cfg eOrig).isSome
  let e ← if sourceFunctionGraph then pure eOrig else Meta.whnf eOrig
  -- Unfold guard: ancestors only (push-on-entry; pop-on-exit holds by
  -- construction, the array lives in the per-call ctx), confirmed structural
  -- equality — a self-similar unfolding terminates as an explicit cycle edge.
  if let some (_, ancestorId) := ctx.ancestors.find? (fun (a, _) => a.equal e) then
    return ancestorId
  let ty ← Meta.inferType e
  -- Open-value holes: one atom per metavariable/hypothesis, under every mode.
  if let some id ← holeAtom? cfg (fun c => walkExpr cfg c { mode, ancestors := ctx.ancestors })
      e ty then
    rememberObservationTerm (cfg.recordTerms || !cfg.observations.isEmpty) e id
    return id
  -- Custom relationalizer wins over any identity instance.
  let tyKey ← Meta.whnf ty
  let isFunctionGraph := sourceFunctionGraph ||
    (cfg.functionGraphs && (← graphSide? e).isSome)
  unless isFunctionGraph do
    if let some id ← customDispatch? eOrig e tyKey
        (fun guardId c =>
          walkExpr cfg c { mode, ancestors := ctx.ancestors.push (e, guardId) }) then
      rememberObservationTerm (cfg.recordTerms || !cfg.observations.isEmpty) e id
      return id
  -- Context mode also seeds this table with witness terms that are not named
  -- function applications, so its lookup remains broader than the identity
  -- rule for genuine graph points.
  if cfg.functionGraphs || sourceFunctionGraph then
    if let some id := (← get).applicationAtoms[(⟨e⟩ : ExprStructEq)]? then
      rememberObservationTerm (cfg.recordTerms || !cfg.observations.isEmpty) e id
      return id
  let symbolicKey? ← symbolicValueKey? cfg mode e tyKey
  if let some key := symbolicKey? then
    if let some id := (← get).symbolicAtoms[(⟨key⟩ : ExprStructEq)]? then
      rememberObservationTerm (cfg.recordTerms || !cfg.observations.isEmpty) e id
      return id
  -- The identity decision (declared mode, closed subterms only).
  let verdict ←
    if !isFunctionGraph && mode == .declared && isClosedValue e then identityVerdict tyKey e
    else pure .fresh
  if let .reuse id := verdict then
    rememberObservationTerm (cfg.recordTerms || !cfg.observations.isEmpty) e id
    return id
  let s ← get
  let (atomId, s) := s.freshId
  set { s with
    provenance := s.provenance.insert atomId e
    observationTerms := if cfg.recordTerms || !cfg.observations.isEmpty then
      s.observationTerms.push (e, atomId) else s.observationTerms
    symbolicAtoms := match symbolicKey? with
      | some key => s.symbolicAtoms.insert ⟨key⟩ atomId
      | none => s.symbolicAtoms }
  -- Register before walking children, so a re-occurrence inside the subtree
  -- (sharing, or a quotient collapsing a child into its parent) resolves to
  -- this atom.
  registerIdentity verdict e atomId
  emitNode cfg (fun c => walkExpr cfg c { mode, ancestors := ctx.ancestors.push (e, atomId) })
    e ty tyKey origName atomId sourceFunctionGraph
  return atomId

private meta def tupleStartsWith (tuple : JsonTuple) (initial : Array String) : Bool := Id.run do
  if tuple.atoms.size != initial.size + 1 then return false
  for index in [:initial.size] do
    if tuple.atoms[index]! != initial[index]! then return false
  return true

/-- Add one requested function application to an existing walk. `source`
    supplies the function name, while `result` and `arguments` may include
    refinements known by a caller. -/
public meta def addObservation (cfg : WalkConfig) (source result : Expr)
    (arguments : Array Expr) (anchors : Array (Expr × String)) :
    StateT WalkState MetaM Unit := do
  let some (relation, _) ← graphSide? source | return
  let mut atomIds := #[]
  let mut types := #[]
  for argument in arguments do
    let atomId ← match anchors.find? (fun (seen, _) => seen.equal argument) with
      | some (_, atomId) => pure atomId
      | none => walkExpr cfg argument
    atomIds := atomIds.push atomId
    types := types.push (← sigOfType (← inferType argument))
  let resultType := ← sigOfType (← inferType result)
  types := types.push resultType
  let reducedResult ← whnf result
  let state ← get
  let mut knownResult? := state.applicationAtoms[(⟨result⟩ : ExprStructEq)]?
  if knownResult?.isNone then
    if let some (declaredTypes, tuples) := state.relations.get? relation then
      if declaredTypes == types then
        for tuple in tuples do
          if tupleStartsWith tuple atomIds then
            knownResult? := tuple.atoms.back?
            break
  let resultId ← match knownResult? with
    | some resultId => pure resultId
    | none =>
      if reducedResult.hasFVar || reducedResult.hasMVar then do
        let state ← get
        let (label, state) := state.freshApplicationLabel
        let (atomId, state) := state.freshId
        set (state.addAtom { id := atomId, type := resultType, label })
        pure atomId
      else
        walkExpr cfg reducedResult
  modify fun state =>
    let applications := state.applicationAtoms
      |>.insert (⟨source⟩ : ExprStructEq) resultId
      |>.insert (⟨result⟩ : ExprStructEq) resultId
      |>.insert (⟨reducedResult⟩ : ExprStructEq) resultId
    { state with applicationAtoms := applications }
  atomIds := atomIds.push resultId
  let state ← get
  if let some (declaredTypes, tuples) := state.relations.get? relation then
    if declaredTypes != types then
      logWarning m!"spytial: '{relation}' names relations of arity \
        {declaredTypes.size} and {types.size}; the observation is not drawn"
      return
    if tuples.any (fun tuple => tuple.atoms == atomIds) then return
  modify fun state => state.addTuple relation types { atoms := atomIds, types }

/-- Replace the sole data argument in an elaborated unary observation while
    preserving its already elaborated implicit arguments. -/
private meta def observationAt (observation argument value : Expr) : Expr :=
  mkAppN observation.getAppFn <| observation.getAppArgs.map fun applicationArgument =>
    if applicationArgument.equal argument then value else applicationArgument

/-- Extend the current datum with each requested function's graph over the
    represented values of its domain type. The domain is snapshotted before
    adding any result atoms, so an observation whose codomain is also its
    domain cannot recursively expand the datum. -/
public meta def addActiveDomainObservations (cfg : WalkConfig)
    (observations : Array Expr) : StateT WalkState MetaM Unit := do
  let activeDomain := (← get).observationTerms
  for observation in observations do
    let some (_, arguments) ← graphSide? observation | continue
    unless arguments.size == 1 do continue
    let argument := arguments[0]!
    let domainType ← inferType argument
    for (value, atomId) in activeDomain do
      let compatible ← liftM <| try
        withoutModifyingState <| withNewMCtxDepth <|
          isDefEq (← inferType value) domainType
      catch _ => pure false
      unless compatible do continue
      let application := observationAt observation argument value
      addObservation cfg application application #[value] #[(value, atomId)]

/-- Walk an expression and produce a complete data instance, keeping the
    subterm each atom was walked from (see `Provenance`).

    `withoutModifyingEnv` because the walk derives instances: persisting them
    would let two modules that draw the same third-party type mint the same
    instance name, and importing both would fail. The result is plain data, so
    nothing outlives the rollback. -/
public meta def relationalizeWithProvenance (e : Expr) (cfg : WalkConfig := {})
    (observations : Array Expr := #[]) : MetaM (JsonDataInstance × Provenance) :=
  withoutModifyingEnv do
    let (_, state) ← StateT.run (s := {}) do
      let observationAwareConfig := { cfg with observations }
      let _ ← walkExpr observationAwareConfig e
      let observationConfig := { observationAwareConfig with functionGraphs := true }
      addActiveDomainObservations observationConfig observations
    return (state.toDataInstance, state.provenance)

/-- Walk an expression and produce a complete data instance. -/
public meta def relationalize (e : Expr) (cfg : WalkConfig := {})
    (observations : Array Expr := #[]) : MetaM JsonDataInstance := do
  return (← relationalizeWithProvenance e cfg observations).1

/-! ## Two-pass reference implementation

The spec, implemented literally: a fresh-atom walk (the as-written machinery,
holes and custom relationalizers included), then a merge pass grouping
occurrences by `(type, identity)` computed by the *same* three-way decision
procedure (`identityVerdict`). Merged-away occurrences drop their outgoing
edges and orphaned atoms are collected, because the fused walker never
re-walks a merged subtree. Lives here so tests can import it; it is not on
any hot path. -/

/-- One pass-1 atom with what the merge pass needs to decide its identity. -/
private meta structure RefRecord where
  atomId : String
  /-- The subterm, post-whnf. -/
  expr : Expr
  /-- Its whnf'd elaborated type. -/
  tyKey : Expr
  /-- The ambient mode at this node. -/
  mode : WalkMode
  /-- Function-graph points never participate in value-identity merging. -/
  functionGraph : Bool

/-- The literal two-pass renderer: returns the root atom id and the data
    instance. Differential oracle target for `walkExpr`. -/
public meta partial def referenceRelationalize (e : Expr) (cfg : WalkConfig := {}) :
    MetaM (String × JsonDataInstance) := do
  let records ← IO.mkRef (#[] : Array RefRecord)
  -- Pass 1: every subterm a fresh atom; modes, holes, the unfold guard, and
  -- custom relationalizers behave exactly as in the fused walker.
  let rec refWalk (eOrig : Expr) (ctx : WalkCtx) : StateT WalkState MetaM String := do
    let origName := eOrig.getAppFn.constName?
    let mode ← shiftForWrappers ctx.mode (← Meta.inferType eOrig)
    let sourceFunctionGraph := (← observedGraphSide? cfg eOrig).isSome
    let e ← if sourceFunctionGraph then pure eOrig else Meta.whnf eOrig
    if let some (_, ancestorId) := ctx.ancestors.find? (fun (a, _) => a.equal e) then
      return ancestorId
    let ty ← Meta.inferType e
    if let some id ← holeAtom? cfg (fun c => refWalk c { mode, ancestors := ctx.ancestors })
        e ty then
      return id
    let tyKey ← Meta.whnf ty
    let isFunctionGraph := sourceFunctionGraph ||
      (cfg.functionGraphs && (← graphSide? e).isSome)
    unless isFunctionGraph do
      if let some id ← customDispatch? eOrig e tyKey
          (fun guardId c => refWalk c { mode, ancestors := ctx.ancestors.push (e, guardId) }) then
        return id
    if cfg.functionGraphs || sourceFunctionGraph then
      if let some id := (← get).applicationAtoms[(⟨e⟩ : ExprStructEq)]? then
        return id
    let symbolicKey? ← symbolicValueKey? cfg mode e tyKey
    if let some key := symbolicKey? then
      if let some id := (← get).symbolicAtoms[(⟨key⟩ : ExprStructEq)]? then return id
    let s ← get
    let (atomId, s) := s.freshId
    set { s with symbolicAtoms := match symbolicKey? with
      | some key => s.symbolicAtoms.insert ⟨key⟩ atomId
      | none => s.symbolicAtoms }
    records.modify (·.push { atomId, expr := e, tyKey, mode, functionGraph := isFunctionGraph })
    emitNode cfg (fun c => refWalk c { mode, ancestors := ctx.ancestors.push (e, atomId) })
      e ty tyKey origName atomId sourceFunctionGraph
    return atomId
  let (rootId, s) ← (refWalk e {}).run {}
  -- Pass 2: group occurrences by (type, identity), first occurrence the
  -- representative. Runs in the pass-1 state so atom ids stay consistent;
  -- the identity tables are still empty (pass 1 never consulted them).
  let recs ← records.get
  let (union, _) ← StateT.run (s := s) do
    let mut union : Std.HashMap String String := {}
    for rec in recs do
      if !rec.functionGraph && rec.mode == .declared && isClosedValue rec.expr then
        match ← identityVerdict rec.tyKey rec.expr with
        | .reuse id => union := union.insert rec.atomId id
        | .fresh => pure ()
        | v => registerIdentity v rec.expr rec.atomId
    pure union
  let mapId := fun a => union.getD a a
  let di := s.toDataInstance
  let root' := mapId rootId
  -- Drop the outgoing edges of merged-away occurrences (their subtrees are
  -- not re-walked by the fused walker), rewrite the remaining endpoints.
  let rels1 := di.relations.filterMap fun r =>
    let ts := r.tuples.filterMap fun t =>
      match t.atoms[0]? with
      | some src => if mapId src != src then none
                    else some { t with atoms := t.atoms.map mapId }
      | none => some t
    -- drop relations the merge emptied, not ones born empty
    if ts.isEmpty && !r.tuples.isEmpty then none else some { r with tuples := ts }
  -- Collect atoms orphaned by the merge: keep the relational component of the
  -- root. Constructor tuples place their owner first, while function graphs
  -- place their result last, so reachability is over tuples as undirected
  -- hyperedges rather than assuming column zero is always the rootward end.
  -- A deliberately-disconnected atom a custom relationalizer might emit is
  -- still dropped here; the oracle does not cover that corner.
  let reach ← do
    let mut reach : Std.HashSet String := ({} : Std.HashSet String).insert root'
    let mut changed := true
    while changed do
      changed := false
      for r in rels1 do
        for t in r.tuples do
          if t.atoms.any reach.contains then
            for a in t.atoms do
              unless reach.contains a do
                reach := reach.insert a
                changed := true
    pure reach
  let atoms' := di.atoms.filter fun a => mapId a.id == a.id && reach.contains a.id
  let rels' := rels1.filterMap fun r =>
    let ts := r.tuples.filter fun t => (t.atoms[0]?.map reach.contains).getD true
    if ts.isEmpty && !r.tuples.isEmpty then none else some { r with tuples := ts }
  return (root', { atoms := atoms', relations := rels' })

end SpytialLean

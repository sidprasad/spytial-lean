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
confirmed structural equality, never bare `Expr.hash`. No instance ⇒ no
merging. The `Raw`/`Viewed` wrappers shift the ambient mode for their
subtree, recognized on the *pre-whnf* type head because `Meta.whnf` melts the
semireducible wrappers. `referenceRelationalize` is a literal two-pass
implementation (fresh atoms, then merge); the fused `walkExpr` is
differentially tested against it. The two agree on the partition; when an
identity is coarser than structural, the drawn representative may differ —
the fused walker draws the first-walked occurrence. -/

/-- How subterms of a type decide identity, resolved once per type per walk
    from its `SpytialIdentity` instance (see `resolveRoute`). -/
public meta inductive IdentityRoute where
  /-- No instance ⇒ no merging: every occurrence a fresh atom (node-local;
      children still consult their own types in `declared` mode). -/
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
  /-- Per-walk cache: whnf'd type → its `Repr` instance, when usable for leaf
      labels (`none` records both "no instance" and "failed to evaluate"). -/
  reprInstCache : ExprStructMap (Option Expr) := {}

/-- Generate a fresh atom ID. -/
public meta def WalkState.freshId (s : WalkState) : String × WalkState :=
  let id := s!"atom_{s.nextId}"
  (id, { s with nextId := s.nextId + 1 })

/-- Register an atom in the state. -/
public meta def WalkState.addAtom (s : WalkState) (atom : JsonAtom) : WalkState :=
  { s with atoms := s.atoms.push atom }

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

/-- Convert accumulated state to a JsonDataInstance. -/
public meta def WalkState.toDataInstance (s : WalkState) : JsonDataInstance :=
  let relations := s.relations.toArray.map fun (name, types, tuples) =>
    { id := name, name := name, types := types, tuples := tuples : JsonRelation }
  { atoms := s.atoms, relations := relations }

/-- Configuration for the expression walker. -/
public meta structure WalkConfig where
  /-- When true, skip Prop-typed fields (data mode). When false, show them (proof mode). -/
  filterProofs : Bool := true
  /-- Largest domain product a function tabulates into; over it, the function
      stays a leaf. -/
  maxTableTuples : Nat := 512

/-- The ambient walk mode. Identity is per-type and declared; the mode is
    per-subtree — it decides only whether declarations are consulted at all. -/
public meta inductive WalkMode where
  /-- Consult `SpytialIdentity τ` for each closed subterm; absent ⇒ fresh atom
      (node-local — children still walk in `declared`). The default. -/
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
private meta def isClosedValue (e : Expr) : Bool :=
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

/-- Resolve how subterms of (whnf'd, closed) type `tyKey` decide identity:
    synthesize `SpytialIdentity tyKey`, expose its presentation with `whnf`,
    and take the structural route only when the instance that resolved *is*
    the derived one (checked against the registered twin's parent name, so an
    instance shadowing a derived one routes as an ordinary classifier — meta
    and eval then agree by construction). Memoized per type in the walk state
    under confirmed structural equality. -/
private meta def resolveRoute (tyKey : Expr) : StateT WalkState MetaM IdentityRoute := do
  if let some r := (← get).routeCache[(⟨tyKey⟩ : ExprStructEq)]? then
    return r
  let r ← do
    try
      match ← synthInstance? (← mkAppM ``SpytialIdentity #[tyKey]) with
      | none => pure .noInstance
      | some inst =>
        let viaW ← whnf (← mkAppOptM ``SpytialIdentity.via #[some tyKey, some inst])
        if viaW.isAppOfArity ``IdentityVia.identity 2 then
          let env ← getEnv
          let structural := match tyKey.getAppFn, inst.getAppFn.constName? with
            | .const h _, some instName =>
              match structuralTwinName? env h with
              | some twin => twin.getPrefix == instName
              | none => false
            | _, _ => false
          pure (if structural then .structural else .classifier viaW.appArg!)
        else if viaW.isAppOfArity ``IdentityVia.eqv 2 then
          pure (.eqvRel viaW.appArg!)
        else
          -- presentation opaque to whnf: `toEqv` is total and correct for
          -- both arms, at group-comparison cost
          pure (.eqvRel (← mkAppM ``IdentityVia.toEqv #[viaW]))
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
    bare hole of its target type. -/
private meta def holeAtom? (e ty : Expr) : StateT WalkState MetaM (Option String) := do
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
    beta but not delta, so a proposition still behind a definition matches no
    instance head: `a ∈ ({x | p x} : Set α)` is `setOf p a`, and nothing is
    declared about `setOf`. Unfolding once and retrying is what lets a
    `Set`-valued codomain tabulate at all. -/
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

`Repr` is for labels, never identity: a non-injective `Repr` merging atoms
would be the hash-collision bug all over again. But when a leaf's type
declares `Repr` and the term is closed, the evaluated rendering beats the
pretty-printed spelling. -/

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
    type declares it, otherwise the pretty-printed expression. A failing
    evaluation disables `Repr` labels for the type for the rest of the walk. -/
private meta def leafLabel (e tyKey : Expr) : StateT WalkState MetaM String := do
  if isClosedValue e && !(← hasValuelessConst e) then
    if let some inst ← getReprInst? tyKey then
      try
        let fmt ← evalFormat (← mkAppOptM ``repr #[none, some inst, some e])
        return fmt.pretty
      catch _ =>
        modify fun s => { s with reprInstCache := s.reprInstCache.insert ⟨tyKey⟩ none }
  ppLabel e

/-- Emit the atom for `e` (already whnf'd; id already allocated) and walk its
    children through `recurse` — the display dispatch shared by the fused
    walker and the two-pass reference. `recurse` closes over the child walk
    context (ambient mode, unfold-guard ancestors). -/
private meta def emitNode (cfg : WalkConfig) (recurse : Expr → StateT WalkState MetaM String)
    (e ty tyKey : Expr) (origName : Option Name) (atomId : String) :
    StateT WalkState MetaM Unit := do
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
              modify fun s => s.addTuple fieldName types
                { atoms := #[atomId, childId], types := types }
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
            let fn := toString fieldName
            unless ← tabulate? cfg recurse fn typeName atomId projReduced do
              let childId ← recurse projReduced
              let types := #[typeName, ← columnSig typeName projReduced]
              modify fun s => s.addTuple fn types
                { atoms := #[atomId, childId], types := types }
      else do
        -- Generic function application or unknown — leaf atom
        let label ← leafLabel e tyKey
        modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
    | _ => do
      -- Not a const application — leaf atom
      let label ← leafLabel e tyKey
      modify fun s => s.addAtom { id := atomId, type := typeName, label := label }

/-- Walk a Lean expression and produce atoms + relations.
    Returns the atom ID assigned to this expression.

    Merging: in `declared` mode, each closed subterm's type resolves
    `SpytialIdentity`; subterms with the same `(type, identity)` are one atom,
    and a repeated identity returns the existing atom without re-walking the
    subtree (the first-walked occurrence is the drawn representative). No
    instance, an open subterm, meta-key failure, or eval failure ⇒ a fresh
    atom, node-local. In `asWritten` mode no instance is consulted at all;
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
  -- WHNF reduce to expose constructors
  let e ← Meta.whnf eOrig
  -- Unfold guard: ancestors only (push-on-entry; pop-on-exit holds by
  -- construction, the array lives in the per-call ctx), confirmed structural
  -- equality — a self-similar unfolding terminates as an explicit cycle edge.
  if let some (_, ancestorId) := ctx.ancestors.find? (fun (a, _) => a.equal e) then
    return ancestorId
  let ty ← Meta.inferType e
  -- Open-value holes: one atom per metavariable/hypothesis, under every mode.
  if let some id ← holeAtom? e ty then
    return id
  -- Custom relationalizer wins over any identity instance.
  let tyKey ← Meta.whnf ty
  if let some id ← customDispatch? eOrig e tyKey
      (fun guardId c => walkExpr cfg c { mode, ancestors := ctx.ancestors.push (e, guardId) }) then
    return id
  -- The identity decision (declared mode, closed subterms only).
  let verdict ←
    if mode == .declared && isClosedValue e then identityVerdict tyKey e
    else pure .fresh
  if let .reuse id := verdict then
    return id
  let s ← get
  let (atomId, s) := s.freshId
  set s
  -- Register before walking children, so a re-occurrence inside the subtree
  -- (sharing, or a quotient collapsing a child into its parent) resolves to
  -- this atom.
  registerIdentity verdict e atomId
  emitNode cfg (fun c => walkExpr cfg c { mode, ancestors := ctx.ancestors.push (e, atomId) })
    e ty tyKey origName atomId
  return atomId

/-- Walk an expression and produce a complete JsonDataInstance. -/
public meta def relationalize (e : Expr) (cfg : WalkConfig := {}) : MetaM JsonDataInstance := do
  let (_, state) ← walkExpr cfg e |>.run {}
  return state.toDataInstance

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
    let e ← Meta.whnf eOrig
    if let some (_, ancestorId) := ctx.ancestors.find? (fun (a, _) => a.equal e) then
      return ancestorId
    let ty ← Meta.inferType e
    if let some id ← holeAtom? e ty then
      return id
    let tyKey ← Meta.whnf ty
    if let some id ← customDispatch? eOrig e tyKey
        (fun guardId c => refWalk c { mode, ancestors := ctx.ancestors.push (e, guardId) }) then
      return id
    let s ← get
    let (atomId, s) := s.freshId
    set s
    records.modify (·.push { atomId, expr := e, tyKey, mode })
    emitNode cfg (fun c => refWalk c { mode, ancestors := ctx.ancestors.push (e, atomId) })
      e ty tyKey origName atomId
    return atomId
  let (rootId, s) ← (refWalk e {}).run {}
  -- Pass 2: group occurrences by (type, identity), first occurrence the
  -- representative. Runs in the pass-1 state so atom ids stay consistent;
  -- the identity tables are still empty (pass 1 never consulted them).
  let recs ← records.get
  let (union, _) ← StateT.run (s := s) do
    let mut union : Std.HashMap String String := {}
    for rec in recs do
      if rec.mode == .declared && isClosedValue rec.expr then
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
  -- Collect atoms orphaned by the merge: keep what is reachable from the root
  -- (source → endpoints per tuple). Note a deliberately-disconnected atom a
  -- custom relationalizer might emit would be dropped here; the oracle does
  -- not cover that corner.
  let reach ← do
    let mut reach : Std.HashSet String := ({} : Std.HashSet String).insert root'
    let mut changed := true
    while changed do
      changed := false
      for r in rels1 do
        for t in r.tuples do
          if let some src := t.atoms[0]? then
            if reach.contains src then
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

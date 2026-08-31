module

public import Lean
public meta import SpytialLean.Types
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Identity

namespace SpytialLean

open Lean Meta

/-! # The relationalizer

Walks an elaborated expression into atoms and relations: a fresh atom per
subterm, then merging the occurrences whose `(type, identity)` agree, identity
being declared per type by `SpytialIdentity`. Keys are compared under confirmed
structural equality, never bare `Expr.hash`. -/

/-- How subterms of a type decide identity, resolved once per type per walk.
    The routes differ in cost: `structural` keys meta-side during the walk,
    `classifier` costs one evaluation per closed subterm, `eqvRel` one compiled
    comparison per existing group. -/
public meta inductive IdentityRoute where
  | noInstance
  | structural
  | classifier (f : Expr)
  | eqvRel (r : Expr)
  deriving Inhabited

/-- Atom id → the subterm that minted it. Holes, hypotheses, and
    custom-relationalizer atoms have no such subterm and are absent. -/
public meta abbrev Provenance := Std.HashMap String Expr

public meta structure WalkState where
  atoms : Array JsonAtom := #[]
  relations : Std.HashMap String (Array String × Array JsonTuple) := {}
  nextId : Nat := 0
  /-- One atom per metavariable, and one per free variable, under every mode:
      substitution structure, not identity policy. -/
  mvarAtoms : Std.HashMap MVarId String := {}
  fvarAtoms : Std.HashMap FVarId String := {}
  /-- A repeated occurrence resolves to the id the relationalizer returned,
      never the discarded pre-allocated one. -/
  customSeen : ExprStructMap String := {}
  routeCache : ExprStructMap IdentityRoute := {}
  /-- `none` = no key computable (stuck non-literal, open child, or a
      dependency only evaluation could key); failures are memoized too. -/
  metaKeyCache : ExprStructMap (Option IdentityKey) := {}
  evalKeyCache : ExprStructMap (Option IdentityKey) := {}
  identityAtoms : Std.HashMap (ExprStructEq × IdentityKey) String := {}
  eqvGroups : ExprStructMap (Array (Expr × String)) := {}
  eqvSeen : ExprStructMap String := {}
  provenance : Provenance := {}
  /-- `r w w` per closed subterm on the `.eqv` route — see `identityVerdict`. -/
  eqvRefl : ExprStructMap Bool := {}
  reprInstCache : ExprStructMap (Option Expr) := {}

public meta def WalkState.freshId (s : WalkState) : String × WalkState :=
  let id := s!"atom_{s.nextId}"
  (id, { s with nextId := s.nextId + 1 })

public meta def WalkState.addAtom (s : WalkState) (atom : JsonAtom) : WalkState :=
  { s with atoms := s.atoms.push atom }

public meta def WalkState.addTuple (s : WalkState) (relName : String) (types : Array String)
    (tuple : JsonTuple) : WalkState :=
  let existing := s.relations.getD relName (types, #[])
  { s with relations := s.relations.insert relName (existing.1, existing.2.push tuple) }

/-- Registered with no tuples, so an empty extension still appears. -/
public meta def WalkState.addRelation (s : WalkState) (relName : String)
    (types : Array String) : WalkState :=
  if s.relations.contains relName then s
  else { s with relations := s.relations.insert relName (types, #[]) }

public meta def WalkState.toDataInstance (s : WalkState) : JsonDataInstance :=
  let relations := s.relations.toArray.map fun (name, types, tuples) =>
    { id := name, name := name, types := types, tuples := tuples : JsonRelation }
  { atoms := s.atoms, relations := relations }

public meta structure WalkConfig where
  /-- When true, skip Prop-typed fields (data mode). When false, show them (proof mode). -/
  filterProofs : Bool := true
  /-- Over this, the function stays a leaf instead of tabulating. -/
  maxTableTuples : Nat := 512

/-- Identity is per-type and declared; the mode is per-subtree, and decides
    only whether declarations are consulted at all. `asWritten` is hereditary
    until a `Viewed` shifts back. -/
public meta inductive WalkMode where
  | declared
  | asWritten
  deriving BEq, Repr, Inhabited

/-- Threaded as an argument, so subtree scoping of the mode and the pop-on-exit
    of the unfold guard hold by construction. -/
public meta structure WalkCtx where
  mode : WalkMode := .declared
  /-- Ancestor subterms with their atom ids, so runaway whnf unfolding of a
      recursive definition terminates as an explicit cycle edge. -/
  ancestors : Array (Expr × String) := #[]

public meta def isProofArg (e : Expr) : MetaM Bool := do
  isProofLikeType (← inferType e)

@[expose] public meta def CustomRelationalizer :=
  Expr → (Expr → StateT WalkState MetaM String) → StateT WalkState MetaM String

/-- Stores the def's *name*, not its value: that is what keeps the entries
    serializable into the `.olean`. -/
public meta initialize spytialRelationalizerExt :
    SimplePersistentEnvExtension (Name × Name) (Std.HashMap Name Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (t, d) => m.insert t d
    addImportedFn := fun arrays =>
      arrays.foldl (fun m arr => arr.foldl (fun m (t, d) => m.insert t d) m) {}
  }

public meta def getSpytialRelationalizerName? (env : Environment) (typeName : Name) : Option Name :=
  spytialRelationalizerExt.getState env |>.get? typeName

/-- `declName` must have type `CustomRelationalizer`. -/
public meta def setSpytialRelationalizer (typeName declName : Name) : CoreM Unit :=
  modifyEnv fun env => spytialRelationalizerExt.addEntry env (typeName, declName)

/-- Keyed by def name + body hash, so an interactive body edit recompiles
    instead of serving the stale closure. -/
public meta initialize spytialRelationalizerCache :
    IO.Ref (Std.HashMap Name (UInt64 × CustomRelationalizer)) ← IO.mkRef {}

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

@[implemented_by getSpytialRelationalizerImpl]
public meta opaque getSpytialRelationalizer? (typeName : Name) : MetaM (Option CustomRelationalizer)

/-! ## Identity resolution -/

/-- An open subterm has no value, hence no identity: it stays as written. -/
private meta def isClosedValue (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && !e.hasLevelParam && !e.hasSorry

/-- Called on the *pre-whnf* type: `whnf` melts the semireducible wrappers, and
    `whnfR` sees through reducible abbreviations but not the wrappers
    themselves. Peeling recurses, so the innermost wrapper wins. -/
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

/-- `none` on any evaluation failure: the caller falls back to a fresh atom,
    leaving other groups undisturbed. -/
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

/-- The structural route is taken only when the instance that resolved *is* the
    derived one, so an instance shadowing a derived one routes as an ordinary
    classifier and meta and eval agree by construction. -/
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
  -- Presentation opaque to whnf. `toEqv` would be total here, but the
  -- `.eqvRel` route memoizes per expression, so an `asWritten` reached that way
  -- would merge on the memo alone. Ask the compiled code first.
  if (← evalBool? (← mkAppM ``IdentityVia.isAsWritten #[viaW])) == some true then
    return .noInstance
  return .eqvRel (← mkAppM ``IdentityVia.toEqv #[viaW])

/-- Declared instance, else `ToIdentityKey` encoding, else structural identity
    derived on demand — the same order, for the same reason, as `depPath`.
    Memoized per type, so the decline warning happens once per walk. -/
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

/-! ## Meta-side keys for derived structural instances -/

private meta unsafe def evalOptionKeyUnsafe (e : Expr) : MetaM (Option IdentityKey) :=
  Meta.evalExpr (Option IdentityKey)
    (mkApp (mkConst ``Option [Level.zero]) (mkConst ``IdentityKey)) e

@[implemented_by evalOptionKeyUnsafe]
private meta opaque evalOptionKeyOpaque (e : Expr) : MetaM (Option IdentityKey)

private meta def evalOptionKey? (e : Expr) : MetaM (Option IdentityKey) := do
  try evalOptionKeyOpaque e catch _ => return none

/-- Generated by `Identity.lean`'s deriving handler; takes the walker's
    dispatch for child keys, then the value. -/
@[expose] public meta def StructuralTwin :=
  (Expr → MetaM (Option IdentityKey)) → Expr → MetaM (Option IdentityKey)

public meta initialize spytialTwinCache :
    IO.Ref (Std.HashMap Name (UInt64 × StructuralTwin)) ← IO.mkRef {}

public meta unsafe def getStructuralTwinImpl (typeName : Name) :
    MetaM (Option StructuralTwin) := do
  let some declName := structuralTwinName? (← getEnv) typeName | return none
  -- A registered twin that doesn't resolve (private-module codegen edge)
  -- degrades to the eval fallback rather than failing the walk.
  let some info := (← getEnv).find? declName | return none
  let bodyHash := (info.value?.map Expr.hash).getD 0
  if let some (h, fn) := (← spytialTwinCache.get).get? declName then
    if h == bodyHash then return some fn
  let fn ← Meta.evalExpr StructuralTwin (mkConst ``StructuralTwin) (mkConst declName)
  spytialTwinCache.modify (·.insert declName (bodyHash, fn))
  return some fn

@[implemented_by getStructuralTwinImpl]
public meta opaque getStructuralTwin? (typeName : Name) : MetaM (Option StructuralTwin)

/-- The twin is born from the same plan as the compiled classifier, so their
    keys agree and both may share one atom table. `none` when no twin loads or
    a child no route can key; the caller then falls back to that classifier. -/
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

/-- Evaluation would pierce the barrier and disagree with the meta side, which
    keys by spelling, so a subterm mentioning one stays fresh instead. -/
private meta def hasOpaqueBarrier (e : Expr) : MetaM Bool := do
  let env ← getEnv
  for c in e.getUsedConstants do
    if ← isIrreducible c then return true
    if env.find? c matches some (.opaqueInfo _) then return true
  return false

/-- `reuse` also means: do not walk the children again. -/
private meta inductive IdVerdict where
  | reuse (id : String)
  | keyed (tyKey : Expr) (k : IdentityKey)
  | grouped (tyKey : Expr)
  | fresh

/-- Lookup and memoization only; allocation and registration are the caller's,
    so the fused walker and the reference merge pass can share this one
    decision procedure. -/
private meta def identityVerdict (tyKey e : Expr) : StateT WalkState MetaM IdVerdict := do
  match ← resolveRoute tyKey with
  | .noInstance => return .fresh
  | .structural =>
    let k? ← do
      match ← structuralKey? e with
      | some k => pure (some k)
      | none =>
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
    -- still has merging arms, so it cannot present `.asWritten`, but `w` itself
    -- must not merge, with an identical spelling least of all.
    let refl ← do
      match (← get).eqvRefl[(⟨w⟩ : ExprStructEq)]? with
      | some b => pure b
      | none =>
        let b := (← evalBool? (mkApp2 r w w)) == some true
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

/-- A hole renders as a leaf but keeps its structural atom type, so a
    `Tree`-shaped hole still occupies a `Tree` slot and `Tree` specs apply.
    Must short-circuit *before* custom-relationalizer dispatch: a value
    decomposer must never be handed a bare hole of its target type. -/
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

/-- A custom `spytial_relationalizer` wins over any identity instance, in every
    mode: it is the decomposition layer, not identity policy. `mkRecurse` gets a
    pre-allocated guard id, which bounds degenerate re-walks of `e` inside the
    relationalizer. -/
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

/-- Falls back to the owner's sig on meta failure, so no value that walked
    before fails now. -/
private meta def columnSig (owner : String) (child : Expr) : MetaM String := do
  try
    return (← sigOfType (← inferType child))
  catch _ =>
    return owner

/-- Lexicographic, with the first binder outermost. -/
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

/-- The retry after `whnf` is needed because synthesis reduces beta but not
    delta: `a ∈ ({x | p x} : Set α)` is `setOf p a`, and nothing is declared
    about `setOf`. -/
private meta def decidableFor? (p : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some inst ← Meta.synthInstance? (← mkAppM ``Decidable #[p]) then
    return some (p, inst)
  let p ← Meta.whnf p
  return (← Meta.synthInstance? (← mkAppM ``Decidable #[p])).map ((p, ·))

/-- `none` is undecided, never a guess. -/
private meta def decideProp? (p : Expr) : MetaM (Option Bool) := do
  try
    let some (p, inst) ← decidableFor? p | return none
    match (← Meta.whnf inst).getAppFn with
    | .const ``Decidable.isTrue _ => return some true
    | .const ``Decidable.isFalse _ => return some false
    | _ => evalBool? (← mkAppOptM ``Decidable.decide #[some p, some inst])
  catch _ => return none

/-- A data codomain gives `(owner, d₁, …, dₖ, result)`; a `Prop` codomain has no
    result column, and emits a tuple exactly where the proposition decides
    true. -/
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
    -- Decide every point before walking any atom, so an undecided point bails
    -- without leaving a trace.
    let mut holds := #[]
    for pt in points do
      let some verdict ← decideProp? (mkAppN fn (pick columns pt)) | return false
      if verdict then holds := holds.push pt
    modify (·.addRelation relName types)
    -- Walk only elements a true tuple names; the reference prunes orphans.
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

Labels only: a non-injective `Repr` feeding identity would merge distinct
atoms. -/

private meta unsafe def evalFormatUnsafe (e : Expr) : MetaM Std.Format :=
  Meta.evalExpr Std.Format (mkConst ``Std.Format) e

@[implemented_by evalFormatUnsafe]
private meta opaque evalFormat (e : Expr) : MetaM Std.Format

private meta def getReprInst? (tyKey : Expr) : StateT WalkState MetaM (Option Expr) := do
  if let some cached := (← get).reprInstCache[(⟨tyKey⟩ : ExprStructEq)]? then
    return cached
  let inst? ← try
      synthInstance? (← mkAppM ``Repr #[tyKey])
    catch _ => pure none
  modify fun s => { s with reprInstCache := s.reprInstCache.insert ⟨tyKey⟩ inst? }
  return inst?

/-- Compiling such a constant yields its type's default instead of failing, so
    `0` would be reported for an `opaque n : Nat` as confidently as for a real
    zero. `@[irreducible]` is not this: it has a body. -/
private meta def hasValuelessConst (e : Expr) : MetaM Bool := do
  let env ← getEnv
  return e.getUsedConstants.any fun n =>
    match env.find? n with
    | some (.opaqueInfo _) | some (.axiomInfo _) => true
    | _ => false

/-- A failure is not memoized against the type: the causes that survive the
    guard above (`extern` with no Lean body, `quot`) belong to the term, so
    poisoning the type would make an unrelated leaf's label depend on walk
    order. -/
private meta def leafLabel (e tyKey : Expr) : StateT WalkState MetaM String := do
  if isClosedValue e && !(← hasValuelessConst e) then
    if let some inst ← getReprInst? tyKey then
      try
        let fmt ← evalFormat (← mkAppOptM ``repr #[none, some inst, some e])
        return fmt.pretty
      catch _ =>
        pure ()
  ppLabel e

/-- The display dispatch shared by the fused walker and the two-pass reference.
    `e` is already whnf'd and `atomId` already allocated; `recurse` closes over
    the child walk context. -/
private meta def emitNode (cfg : WalkConfig) (recurse : Expr → StateT WalkState MetaM String)
    (e ty tyKey : Expr) (origName : Option Name) (atomId : String) :
    StateT WalkState MetaM Unit := do
  match e with
  | .lit (.natVal n) =>
    modify fun s => s.addAtom { id := atomId, type := "Nat", label := toString n }

  | .lit (.strVal str) =>
    modify fun s => s.addAtom { id := atomId, type := "String", label := s!"\"{str}\"" }

  | .lam binderName _ _ _ => do
    let typeName ← sigOfType ty
    let label := match origName with
      | some n => shortName n
      | none => s!"λ {binderName}"
    modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
    -- No owning field here, so the function itself is column 0.
    let _ ← tabulate? cfg recurse "maps" typeName atomId e

  | _ => do
    let typeName ← sigOfType ty

    match e.getAppFn with
    | .const fnName _ => do
      let env ← getEnv
      if let some (.ctorInfo ci) := env.find? fnName then
        let ctorShortName := shortName fnName
        modify fun s => s.addAtom { id := atomId, type := typeName, label := ctorShortName }
        let binderNames := ctorDataBinderNames ci
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
      -- A match stuck because iota can't fire on a hole or hypothesis
      -- discriminant. Motive and alternatives are plumbing, so only the
      -- discriminants get edges.
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
          let label ← ppLabel e
          modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
      else if (← typeHead? ty).any (isStructure env ·) then
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
        let label ← leafLabel e tyKey
        modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
    | _ => do
      let label ← leafLabel e tyKey
      modify fun s => s.addAtom { id := atomId, type := typeName, label := label }

/-- Returns the atom id for `e`. A repeated identity returns the existing atom
    without re-walking the subtree, so the first-walked occurrence is the drawn
    representative. -/
public meta partial def walkExpr (cfg : WalkConfig := {}) (eOrig : Expr)
    (ctx : WalkCtx := {}) : StateT WalkState MetaM String := do
  -- Before whnf unfolds it.
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
      (fun guardId c => walkExpr cfg c { mode, ancestors := ctx.ancestors.push (e, guardId) }) then
    return id
  let verdict ←
    if mode == .declared && isClosedValue e then identityVerdict tyKey e
    else pure .fresh
  if let .reuse id := verdict then
    return id
  let s ← get
  let (atomId, s) := s.freshId
  set { s with provenance := s.provenance.insert atomId e }
  -- Register before walking children, so a re-occurrence inside the subtree
  -- resolves to this atom.
  registerIdentity verdict e atomId
  emitNode cfg (fun c => walkExpr cfg c { mode, ancestors := ctx.ancestors.push (e, atomId) })
    e ty tyKey origName atomId
  return atomId

/-- `withoutModifyingEnv` because the walk derives instances: persisting them
    would let two modules that draw the same third-party type mint the same
    instance name, and importing both would fail. -/
public meta def relationalizeWithProvenance (e : Expr) (cfg : WalkConfig := {}) :
    MetaM (JsonDataInstance × Provenance) :=
  withoutModifyingEnv do
    let (_, state) ← walkExpr cfg e |>.run {}
    return (state.toDataInstance, state.provenance)

public meta def relationalize (e : Expr) (cfg : WalkConfig := {}) : MetaM JsonDataInstance := do
  return (← relationalizeWithProvenance e cfg).1

/-! ## Two-pass reference implementation

The spec implemented literally, as the differential oracle `walkExpr` is tested
against. It shares `identityVerdict`, so only the fusion is under test. Not on
any hot path; it lives here so tests can import it. -/

private meta structure RefRecord where
  atomId : String
  expr : Expr
  tyKey : Expr
  mode : WalkMode

public meta partial def referenceRelationalize (e : Expr) (cfg : WalkConfig := {}) :
    MetaM (String × JsonDataInstance) := do
  let records ← IO.mkRef (#[] : Array RefRecord)
  -- Pass 1: every subterm a fresh atom.
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
  -- Pass 2: group by (type, identity), first occurrence the representative.
  -- Runs in the pass-1 state so atom ids stay consistent; the identity tables
  -- are still empty, pass 1 never having consulted them.
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
  -- Drop the outgoing edges of merged-away occurrences: the fused walker does
  -- not re-walk their subtrees.
  let rels1 := di.relations.filterMap fun r =>
    let ts := r.tuples.filterMap fun t =>
      match t.atoms[0]? with
      | some src => if mapId src != src then none
                    else some { t with atoms := t.atoms.map mapId }
      | none => some t
    -- drop relations the merge emptied, not ones born empty
    if ts.isEmpty && !r.tuples.isEmpty then none else some { r with tuples := ts }
  -- A deliberately-disconnected atom a custom relationalizer emits would be
  -- dropped here; the oracle does not cover that corner.
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

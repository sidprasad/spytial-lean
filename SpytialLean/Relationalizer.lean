module

public import Lean
public meta import SpytialLean.Types
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Identity

namespace SpytialLean

open Lean Meta

/-! # The relationalizer

Walks an elaborated expression into atoms and relations. The spec of one
render, literally: **give every subterm a fresh atom, then merge occurrences
with the same identity** — identity declared per type by `SpytialIdentity`,
the atom table keyed on `(type, identity)` with the full whnf'd elaborated
type under confirmed structural equality (never bare `Expr.hash`). No
instance ⇒ no merging: the term draws as written, literals included.

The walk carries an ambient mode: `declared` (consult `SpytialIdentity`;
absent ⇒ fresh atom, node-local) or `asWritten` (no instance consultation,
hereditary). The `Raw`/`Viewed` wrappers shift the mode for their subtree and
are recognized on the *pre-whnf* type head, because `Meta.whnf` melts the
semireducible wrappers themselves — which is also why no wrapper atom ever
appears.

`referenceRelationalize` implements the two-pass spec verbatim (fresh-atom
walk, then a merge pass computing identity the same three ways); the fused
`walkExpr` is differentially tested against it. -/

/-- How subterms of a type decide identity, resolved once per type per walk
    from its `SpytialIdentity` instance (see `resolveRoute`). -/
public meta inductive IdentityRoute where
  /-- No instance ⇒ no merging: every occurrence a fresh atom (node-local;
      children still consult their own types in `declared` mode). -/
  | noInstance
  /-- The derived structural instance (extension marker + classifier
      presentation): keys are computed meta-side during the walk, zero
      `evalExpr`. -/
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

/-- Register a relation with no tuples, leaving an existing one alone. An empty
    extension is content — a relation that decidably never holds — not the same
    thing as a relation nobody computed. -/
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

/-- The ambient walk mode (the doc's walk-modes table). Identity is per-type
    and declared; the mode is per-subtree and contextual — it decides only
    whether declarations are consulted at all. -/
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

Three ways a type's identity is computed, per its instance: the derived
structural key is reproduced meta-side (zero `evalExpr`); a non-derived
classifier costs one evaluation per closed subterm; a decider costs one
compiled comparison per existing group. Open subterms have no value, hence no
identity: fresh atoms, node-local. -/

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

/-- The opacity gate: a leaf whose head constant is `@[irreducible]` or
    `opaque` keys by its spelling — the default disciplines do not unfold or
    evaluate through deliberate barriers. (`toString` on `Expr` is
    `dbgToString`: context-free and structurally faithful, so distinct stuck
    terms never share a spelling key; `IdentityKey.ofSpelling` is its own
    constructor, so a spelling never collides with a genuine key.) Explicit
    `.identity`/`.eqv` instances run the user's function as-is: barriers hold
    against defaults, not against declarations. -/
private meta def opacityKey? (v : Expr) : MetaM (Option IdentityKey) := do
  let w ← whnf v
  let .const c _ := w.getAppFn | return none
  if ← isIrreducible c then return some (.ofSpelling (toString w))
  if (← getConstInfo c) matches .opaqueInfo _ then return some (.ofSpelling (toString w))
  return none

-- TODO(norm?-display): when a type's instance carries `norm? := some n`, the
-- design's display layer draws the structure of `n e` for each *new* group.
-- Doing that from the walker requires reifying the evaluated `n e` back into
-- an `Expr`, i.e. a `ToExpr α` for arbitrary user types — no such reification
-- is generally available, so `norm?` display is deferred to a later commit
-- rather than shipping a half-working path. Merging is unaffected either way,
-- by the law `identity (norm x) = identity x`.

/-- Resolve how subterms of (whnf'd, closed) type `tyKey` decide identity:
    synthesize `SpytialIdentity tyKey`, expose its presentation with `whnf`,
    and recognize the derived structural case via the extension marker.
    Memoized per type in the walk state under confirmed structural equality.

    Known edge: the marker asserts "this type's instance *is* the derived
    structural one"; an instance shadowing a derived one with a different
    classifier would be mis-keyed meta-side. Shadowing a derived instance
    violates the coherence discipline the design leans on, so the marker is
    trusted. -/
public meta def resolveRoute (tyKey : Expr) : StateT WalkState MetaM IdentityRoute := do
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
          let structural := match tyKey.getAppFn with
            | .const h _ => isSpytialStructural env h
            | _ => false
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

/-! ## Meta-side reproduction of derived structural keys

The derived key functions (see `Identity.lean`'s deriving handler) are
reproduced during the walk with zero `evalExpr`: constructor tag + child keys,
fields routed exactly as the field rule baked them — `SpytialIdentity` when an
instance is declared, else the library `ToIdentityKey` encodings. The exact
key shapes are pinned by `tests/IdentityTest.lean` and cross-checked against
the compiled classifiers in the walker tests. -/

/-- `some n` for a value of type `Nat`, without evaluating through opacity
    barriers (default-transparency `whnf` only). -/
private meta partial def natValue? (v : Expr) : MetaM (Option Nat) := do
  if let some n ← getNatValue? v then return some n
  let w ← whnf v
  if let some n := getRawNatValue? w then return some n
  if let some n ← getNatValue? w then return some n
  if w.isAppOfArity ``Nat.succ 1 then
    if let some n ← natValue? w.appArg! then return some (n + 1)
  return none

/-- Drill a numeric wrapper's whnf normal form — nested single-data-field
    constructors (`Char.mk`/`UInt8.ofBitVec`/`BitVec.ofFin`/`Fin.mk`, …) —
    down to the underlying `Nat` literal: exactly the `.toNat` the
    corresponding encodings write. -/
private meta partial def drillNatValue? (v : Expr) (fuel : Nat := 8) : MetaM (Option Nat) := do
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let w ← whnf v
    if let some n := getRawNatValue? w then return some n
    let .const c _ := w.getAppFn | return none
    let some (.ctorInfo ci) := (← getEnv).find? c | return none
    let args := w.getAppArgs
    let mut dataField? : Option Expr := none
    for f in args.extract ci.numParams args.size do
      unless ← isProofLikeType (← inferType f) do
        if dataField?.isSome then return none
        dataField? := some f
    let some f := dataField? | return none
    drillNatValue? f fuel

/-- Collect the element expressions of a literal `List` value. -/
private meta partial def listElems? (v : Expr) (acc : Array Expr := #[]) :
    MetaM (Option (Array Expr)) := do
  let w ← whnf v
  if w.isAppOfArity ``List.nil 1 then return some acc
  if w.isAppOfArity ``List.cons 3 then
    let args := w.getAppArgs
    return ← listElems? args[2]! (acc.push args[1]!)
  return none

private meta def intKeyOf : Int → IdentityKey
  | .ofNat n => .ofList [.ofString "ofNat", .ofNat n]
  | .negSucc n => .ofList [.ofString "negSucc", .ofNat n]

mutual

/-- Meta-side reproduction of the library `ToIdentityKey` encodings, dispatched
    on the (whnf'd) field type's head. Unknown heads (user encodings) are not
    reproducible ⇒ `none`, failing the enclosing derived key. A stuck value of
    a known head keys by its spelling when deliberately opaque (the opacity
    gate), else fails. -/
private meta partial def encodedKey? (ty v : Expr) : MetaM (Option IdentityKey) := do
  let some h := ty.getAppFn.constName? | return none
  match ← encodedKeyDirect? h ty v with
  | some k => return some k
  | none => opacityKey? v

/-- The per-head encoding logic of `encodedKey?`, without the opacity
    fallback. -/
private meta partial def encodedKeyDirect? (h : Name) (ty v : Expr) :
    MetaM (Option IdentityKey) := do
  match h with
  | ``Nat => return (← natValue? v).map .ofNat
  | ``String =>
    if let some s := getStringValue? v then return some (.ofString s)
    return (getStringValue? (← whnf v)).map .ofString
  | ``Bool =>
    let w ← whnf v
    if w.isConstOf ``Bool.true then return some (.ofNat 1)
    if w.isConstOf ``Bool.false then return some (.ofNat 0)
    return none
  | ``Char =>
    if let some c ← getCharValue? v then return some (.ofNat c.toNat)
    return (← drillNatValue? v).map .ofNat
  | ``Int =>
    if let some i ← getIntValue? v then return some (intKeyOf i)
    let w ← whnf v
    if w.isAppOfArity ``Int.ofNat 1 then
      return (← natValue? w.appArg!).map (intKeyOf <| .ofNat ·)
    if w.isAppOfArity ``Int.negSucc 1 then
      return (← natValue? w.appArg!).map (intKeyOf <| .negSucc ·)
    if let some i ← getIntValue? w then return some (intKeyOf i)
    return none
  | ``UInt8 | ``UInt16 | ``UInt32 | ``UInt64 | ``USize =>
    return (← drillNatValue? v).map .ofNat
  | ``List =>
    let some elems ← listElems? v | return none
    let elemTy ← whnf ty.appArg!
    let mut parts := #[IdentityKey.ofString "list"]
    for el in elems do
      let some k ← encodedKey? elemTy el | return none
      parts := parts.push k
    return some (.ofList parts.toList)
  | ``Array =>
    let w ← whnf v
    unless w.isAppOfArity ``Array.mk 2 do return none
    let some elems ← listElems? w.appArg! | return none
    let elemTy ← whnf ty.appArg!
    let mut parts := #[IdentityKey.ofString "array"]
    for el in elems do
      let some k ← encodedKey? elemTy el | return none
      parts := parts.push k
    return some (.ofList parts.toList)
  | ``Option =>
    let w ← whnf v
    if w.isAppOfArity ``Option.none 1 then
      return some (.ofList [.ofString "none"])
    if w.isAppOfArity ``Option.some 2 then
      let some k ← encodedKey? (← whnf ty.appArg!) w.appArg! | return none
      return some (.ofList [.ofString "some", k])
    return none
  | ``Prod =>
    let w ← whnf v
    unless w.isAppOfArity ``Prod.mk 4 do return none
    let tyArgs := ty.getAppArgs
    let vArgs := w.getAppArgs
    let some k1 ← encodedKey? (← whnf tyArgs[0]!) vArgs[2]! | return none
    let some k2 ← encodedKey? (← whnf tyArgs[1]!) vArgs[3]! | return none
    return some (.ofList [.ofString "prod", k1, k2])
  | _ => return none

end

mutual

/-- Meta-side reproduction of the derived structural identity key of `e` —
    bottom-up from constructor names and child keys, zero `evalExpr`,
    memoized per (whnf'd) subterm. `none` when the key cannot be computed
    meta-side (open child, stuck non-literal, or a dependency only evaluation
    could key): the subterm and its ancestors within the derived walk fall
    back to fresh atoms. A stuck leaf with an `@[irreducible]`/`opaque` head
    keys by its spelling instead (the opacity gate). Only meaningful for
    types whose route is `.structural`. -/
public meta partial def structuralKey? (e : Expr) : StateT WalkState MetaM (Option IdentityKey) := do
  if !isClosedValue e then return none
  let w ← whnf e
  if let some r := (← get).metaKeyCache[(⟨w⟩ : ExprStructEq)]? then
    return r
  let r ← do
    match w.getAppFn with
    | .const c _ =>
      if let some (.ctorInfo ci) := (← getEnv).find? c then
        let args := w.getAppArgs
        let mut parts := #[IdentityKey.ofString (shortName c)]
        let mut ok := true
        for arg in args.extract ci.numParams args.size do
          -- proof-like fields are erased from identity, exactly as the
          -- derived key functions skip them
          if ← isProofArg arg then
            continue
          match ← fieldKey? arg with
          | some k => parts := parts.push k
          | none => ok := false; break
        pure (if ok then some (.ofList parts.toList) else none)
      else
        opacityKey? w
    | _ => pure none
  modify fun s => { s with metaKeyCache := s.metaKeyCache.insert ⟨w⟩ r }
  return r

/-- The field rule at walk time, mirroring the deriving handler's `depPath`:
    a field routes through its type's `SpytialIdentity` when an instance is
    declared — meta-computable only for derived structural instances — else
    through the library `ToIdentityKey` encodings. -/
public meta partial def fieldKey? (arg : Expr) : StateT WalkState MetaM (Option IdentityKey) := do
  let ty ← whnf (← inferType arg)
  match ← resolveRoute ty with
  | .structural => structuralKey? arg
  | .classifier _ | .eqvRel _ =>
    -- identity-routed, but the classifier/decider is a user function the walk
    -- cannot reproduce meta-side ⇒ the enclosing derived key fails (fresh
    -- atoms), per the meta-failure rule
    return none
  | .noInstance => encodedKey? ty arg

end

/-! ## The identity decision -/

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
    match ← structuralKey? e with
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

/-- The type sig of a relation's target column: the child's own, named exactly
    as the child atom's `type` is. Falls back to the owner's on any meta
    failure, so no value that walked before fails now. -/
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

/-- Read a point off the columns it indexes. -/
private meta def pick [Inhabited α] (columns : Array (Array α)) (pt : Array Nat) : Array α :=
  Id.run do
    let mut picked := #[]
    for col in [:pt.size] do
      picked := picked.push columns[col]![pt[col]!]!
    return picked

/-- The verdict of a closed proposition: synthesize `Decidable p` and reduce the
    instance to its constructor. Compiled evaluation of `decide p` is the one
    fallback for an instance `whnf` leaves stuck. `none` — no instance, or
    neither route settles it — is a genuine "undecided", never a guess. -/
private meta def decideProp? (p : Expr) : MetaM (Option Bool) := do
  try
    let some inst ← Meta.synthInstance? (← mkAppM ``Decidable #[p]) | return none
    match (← Meta.whnf inst).getAppFn with
    | .const ``Decidable.isTrue _ => return some true
    | .const ``Decidable.isFalse _ => return some false
    | _ => evalBool? (← mkAppOptM ``Decidable.decide #[some p, some inst])
  catch _ => return none

/-- Emit `relName` as the flat table over the enumerable domain product, in
    lexicographic order with the first binder outermost; report whether it
    fired.

    A data codomain gives `(owner, d₁, …, dₖ, result)`, every point a tuple. A
    `Prop` codomain gives `(owner, d₁, …, dₖ)` — a proposition-valued function
    *is* a relation, so its extension is where it decidably holds and there is
    no result column. Domain elements are walked once per column and their ids
    repeat across tuples, so whether a domain value and a result end up one atom
    stays the identity layer's decision. -/
private meta def tabulate? (cfg : WalkConfig) (recurse : Expr → StateT WalkState MetaM String)
    (relName ownerSig ownerId : String) (value : Expr) : StateT WalkState MetaM Bool := do
  let some plan ← tabulationPlan? (← inferType value) | return false
  unless plan.size ≤ cfg.maxTableTuples do return false
  -- an opaque or stuck function keeps its leaf
  let fn@(.lam ..) ← Meta.whnf value | return false
  let types := #[ownerSig] ++ (← plan.tailTypes.mapM (sigOfType ·))
  let columns := plan.binders.map (·.elems.map (·.2))
  let points := plan.points
  match plan.kind with
  | .data =>
    let ids ← columns.mapM (·.mapM recurse)
    for pt in points do
      let resId ← recurse (← Meta.whnf (mkAppN fn (pick columns pt)))
      let atoms := #[ownerId] ++ pick ids pt ++ #[resId]
      modify fun s => s.addTuple relName types { atoms, types }
    return true
  | .prop =>
    -- every point decides before any atom is walked, so an undecided point
    -- bails the whole table without a trace: a missing tuple would assert a
    -- non-relatedness nothing established
    let mut holds := #[]
    for pt in points do
      let some verdict ← decideProp? (mkAppN fn (pick columns pt)) | return false
      if verdict then holds := holds.push pt
    modify (·.addRelation relName types)
    -- only elements some true tuple names get walked: an element reachable
    -- through no tuple is an orphan the two-pass reference prunes, and the
    -- differential would split
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
      -- stuck match (iota can't fire on a hole/hypothesis discriminant): one
      -- ternary `scrutinee` (match, position, discriminant) whatever the
      -- discriminant count; motive and alternatives are plumbing
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
  -- representative. Runs in the pass-1 state: caches are warm, the identity
  -- tables are still empty.
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
    -- a relation born empty (a decidable table that never holds) is content;
    -- only one emptied by the merge is a casualty
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

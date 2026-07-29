module

public import Lean
public meta import SpytialLean.Types
public meta import SpytialLean.TypeShape

namespace SpytialLean

open Lean Meta

/-- State maintained while walking an expression tree. -/
public meta structure WalkState where
  atoms : Array JsonAtom := #[]
  /-- Map from relation name to accumulated tuples. -/
  relations : Std.HashMap String (Array String × Array JsonTuple) := {}
  /-- Whnf'd subterm → atom ID. Structural dedup: hash-bucketed but confirmed with
      `Expr.equal`, so repeated sub-values share one atom and a hash collision cannot
      merge distinct values. Also guards recursion. -/
  seen : ExprStructMap String := {}
  /-- Per-walk cache: whnf'd type → its `BEq` instance, when usable for
      declared-equality merging (`none` records both "no instance" and
      "instance failed to evaluate"). -/
  beqInstCache : ExprStructMap (Option Expr) := {}
  /-- Declared-equality representatives per type head: (whnf'd expr, atom id). -/
  repsByType : Std.HashMap Name (Array (Expr × String)) := {}
  nextId : Nat := 0

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

/-- Record the atom ID assigned to a (whnf'd) expression. -/
public meta def WalkState.markSeen (s : WalkState) (e : Expr) (atomId : String) : WalkState :=
  { s with seen := s.seen.insert ⟨e⟩ atomId }

/-- Convert accumulated state to a JsonDataInstance. -/
public meta def WalkState.toDataInstance (s : WalkState) : JsonDataInstance :=
  let relations := s.relations.toArray.map fun (name, types, tuples) =>
    { id := name, name := name, types := types, tuples := tuples : JsonRelation }
  { atoms := s.atoms, relations := relations }

/-- Which equivalence decides when two subterms map to the same atom. -/
public meta inductive IdentityMode where
  /-- Structural equality of whnf'd subterms only (the `seen` memo). -/
  | syntactic
  /-- Also merge closed subterms that the type's declared `BEq` calls equal. -/
  | declared
  /-- Also merge definitionally equal subterms (`Meta.isDefEq`); reaches open terms. -/
  | defeq

/-- Configuration for the expression walker. -/
public meta structure WalkConfig where
  /-- When true, skip Prop-typed fields (data mode). When false, show them (proof mode). -/
  filterProofs : Bool := true
  /-- Identity ladder level; see `IdentityMode`. -/
  identityMode : IdentityMode := .declared

/-- Check if an expression is a proof or type (erased at runtime). -/
public meta def isProofArg (e : Expr) : MetaM Bool := do
  let ty ← inferType e
  -- Use Meta.isProp for proper sort-level check (handles ∀-typed proofs)
  let isProp ← Meta.isProp ty
  return isProp || ty.isSort

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

/-- Session-local cache of *compiled* relationalizer functions keyed by def name, so a
    registered def is evaluated at most once per process. The persistent extension is
    the source of truth; this only memoizes the `evalExpr`. -/
public meta initialize spytialRelationalizerCache :
    IO.Ref (Std.HashMap Name CustomRelationalizer) ← IO.mkRef {}

/-- Compile (with memoization) the custom relationalizer registered for `typeName`. -/
public meta unsafe def getSpytialRelationalizerImpl (typeName : Name) :
    MetaM (Option CustomRelationalizer) := do
  let some declName := getSpytialRelationalizerName? (← getEnv) typeName | return none
  if let some fn := (← spytialRelationalizerCache.get).get? declName then
    return some fn
  let fn ← Meta.evalExpr CustomRelationalizer (mkConst ``CustomRelationalizer) (mkConst declName)
  spytialRelationalizerCache.modify (·.insert declName fn)
  return some fn

/-- Look up the custom relationalizer registered for a type name, if any. Reads the
    persistent name registry, then evaluates the named def (memoized per process). -/
@[implemented_by getSpytialRelationalizerImpl]
public meta opaque getSpytialRelationalizer? (typeName : Name) : MetaM (Option CustomRelationalizer)

/-- Try to enumerate all elements of a finite type.
    Returns `some [(label, expr)]` for finite types, `none` otherwise. -/
public meta def tryEnumerateDomain (ty : Expr) : MetaM (Option (Array (String × Expr))) := do
  let ty ← Meta.whnf ty
  match ty.getAppFn with
  | .const ``Fin _ =>
    let args := ty.getAppArgs
    if h : args.size = 1 then
      let nExpr ← Meta.whnf args[0]
      match nExpr with
      | .lit (.natVal n) =>
        if n ≤ 20 then
          let mut result : Array (String × Expr) := #[]
          for i in [:n] do
            -- Use OfNat instance to construct Fin element
            let iExpr := mkNatLit i
            let finExpr ← Meta.mkAppOptM ``OfNat.ofNat #[some ty, some iExpr, none]
            result := result.push (toString i, finExpr)
          return some result
        else return none
      | _ => return none
    else return none
  | .const ``Bool _ =>
    return some #[("false", mkConst ``Bool.false), ("true", mkConst ``Bool.true)]
  | .const indName _ =>
    -- Check for zero-arity enumerative inductives
    let env ← getEnv
    if let some (.inductInfo ii) := env.find? indName then
      if ii.numIndices == 0 && ii.numParams == 0 then
        let allZeroArity := ii.ctors.all fun ctorName =>
          match env.find? ctorName with
          | some (.ctorInfo ci) => ci.numFields == 0
          | _ => false
        if allZeroArity then
          let result := ii.ctors.toArray.map fun ctorName =>
            (shortName ctorName, mkConst ctorName)
          return some result
        else return none
      else return none
    else return none
  | _ => return none

/-! ### Declared-equality identity

When a type carries a `BEq` instance (including one derived from `DecidableEq` via
`instBEqOfDecidableEq`), that instance — not the syntactic spelling of a term — is the
user's notion of equality, so closed subterms it calls equal share one atom. -/

private meta unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool :=
  Meta.evalExpr Bool (mkConst ``Bool) e

/-- Evaluate a closed `Bool`-valued expression (declared-equality checks). -/
@[implemented_by evalBoolUnsafe]
private meta opaque evalBool (e : Expr) : MetaM Bool

/-- The `BEq` instance for the (whnf'd) type, synthesized at most once per walk per
    type. `Prop`s are ineligible for free: `BEq : Type u → Type u` never synthesizes
    for them. -/
meta def getBEqInst? (tyWhnf : Expr) : StateT WalkState MetaM (Option Expr) := do
  if let some cached := (← get).beqInstCache.get? ⟨tyWhnf⟩ then
    return cached
  let inst? ← try
      Meta.synthInstance? (← Meta.mkAppM ``BEq #[tyWhnf])
    catch _ => pure none
  modify fun s => { s with beqInstCache := s.beqInstCache.insert ⟨tyWhnf⟩ inst? }
  return inst?

/-- Outcome of a declared-equality lookup for a subterm. -/
meta inductive DeclaredEq where
  /-- The type's `BEq` matched an existing representative carrying this atom id. -/
  | merged (atomId : String)
  /-- Eligible type but no equal representative: record the subterm as a new one. -/
  | newRep
  /-- No usable `BEq` on this type. -/
  | ineligible

/-- Compare `e` (whnf'd, closed) against the representatives of its type under the
    type's declared `BEq`. An evaluation failure marks the whole type unusable, so a
    broken or noncomputable instance is attempted only once per walk. -/
meta def tryDeclaredEq (e tyWhnf : Expr) (typeHead : Name) :
    StateT WalkState MetaM DeclaredEq := do
  let some inst ← getBEqInst? tyWhnf | return .ineligible
  for (rep, repId) in (← get).repsByType.getD typeHead #[] do
    let isEq ← try
        evalBool (← Meta.mkAppOptM ``BEq.beq #[none, some inst, some rep, some e])
      catch _ =>
        modify fun s => { s with beqInstCache := s.beqInstCache.insert ⟨tyWhnf⟩ none }
        return .ineligible
    if isEq then
      return .merged repId
  return .newRep

/-- Walk a Lean expression and produce atoms + relations.
    Returns the atom ID assigned to this expression. -/
public meta partial def walkExpr (cfg : WalkConfig := {}) (eOrig : Expr) : StateT WalkState MetaM String := do
  -- Save original name before WHNF unfolds it
  let origName := eOrig.getAppFn.constName?
  -- WHNF reduce to expose constructors
  let e ← Meta.whnf eOrig

  -- Structural dedup (and recursion guard): a repeated sub-value resolves to the
  -- atom already emitted for it.
  let s ← get
  if let some existingId := s.seen.get? ⟨e⟩ then
    return existingId

  let ty ← Meta.inferType e

  -- The custom-relationalizer lookup happens up front: an explicit registration is
  -- the strongest user intent, so it also disables declared-equality merging.
  let tyWhnfForLookup ← Meta.whnf ty
  let tyHeadName? : Option Name :=
    if let .const n _ := tyWhnfForLookup.getAppFn then some n else none
  let customRel? ← match tyHeadName? with
    | some n => getSpytialRelationalizer? n
    | none => pure none

  -- Declared equality: a closed subterm of a type with `BEq` collapses onto the
  -- first representative the instance calls equal. Literals are skipped: whnf'd
  -- literals are already syntactically canonical, so a lawful `BEq` could never
  -- merge distinct ones.
  let mut newRepOf? : Option Name := none
  if !(cfg.identityMode matches .syntactic) && customRel?.isNone && !e.isLit
      && !e.hasFVar && !e.hasMVar && !e.hasLevelParam then
    if let some typeHead := tyHeadName? then
      match ← tryDeclaredEq e tyWhnfForLookup typeHead with
      | .merged repId =>
        modify (·.markSeen e repId)
        return repId
      | .newRep => newRepOf? := some typeHead
      | .ineligible => pure ()

  -- Allocate a fresh ID and mark as seen immediately (before recursing)
  let s ← get
  let (atomId, s) := s.freshId
  let s := s.markSeen e atomId
  set s
  if let some typeHead := newRepOf? then
    modify fun s => { s with
      repsByType := s.repsByType.insert typeHead
        ((s.repsByType.getD typeHead #[]).push (e, atomId)) }

  if let some relFn := customRel? then
    return ← relFn eOrig (walkExpr cfg)

  -- Dispatch by expression form
  match e with
  -- Nat literal
  | .lit (.natVal n) =>
    modify fun s => s.addAtom { id := atomId, type := "Nat", label := toString n }
    return atomId

  -- String literal
  | .lit (.strVal str) =>
    modify fun s => s.addAtom { id := atomId, type := "String", label := s!"\"{str}\"" }
    return atomId

  -- Lambda — try to enumerate finite domain, otherwise labeled node
  | .lam binderName binderType _body _bi => do
    let typeName ← sigOfType ty
    let label := match origName with
      | some n => shortName n
      | none => s!"λ {binderName}"
    modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
    -- Try finite enumeration of the domain
    let domainElems ← tryEnumerateDomain binderType
    match domainElems with
    | some elems =>
      for (elemLabel, elemExpr) in elems do
        let result ← Meta.whnf (Expr.app e elemExpr)
        let childId ← walkExpr cfg result
        modify fun s => s.addTuple elemLabel #[typeName, typeName]
          { atoms := #[atomId, childId], types := #[typeName, typeName] }
    | none => pure ()  -- non-finite domain, just a labeled node
    return atomId

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
            let childId ← walkExpr cfg arg
            let fieldName := fieldRelName ctorShortName binderNames i
            modify fun s => s.addTuple fieldName #[typeName, typeName]
              { atoms := #[atomId, childId], types := #[typeName, typeName] }
        return atomId
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
            let childId ← walkExpr cfg projReduced
            let fn := toString fieldName
            modify fun s => s.addTuple fn #[typeName, typeName]
              { atoms := #[atomId, childId], types := #[typeName, typeName] }
        return atomId
      else do
        -- Generic function application or unknown — leaf atom
        let label ← ppLabel e
        modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
        return atomId
    | _ => do
      -- Not a const application — leaf atom
      let label ← ppLabel e
      modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
      return atomId

/-- Walk an expression and produce a complete JsonDataInstance. -/
public meta def relationalize (e : Expr) (cfg : WalkConfig := {}) : MetaM JsonDataInstance := do
  let (_, state) ← walkExpr cfg e |>.run {}
  return state.toDataInstance

end SpytialLean

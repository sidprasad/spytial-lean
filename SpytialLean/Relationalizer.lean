import Lean
import SpytialLean.Types

namespace SpytialLean

open Lean Meta

/-- State maintained while walking an expression tree. -/
structure WalkState where
  atoms : Array JsonAtom := #[]
  /-- Map from relation name to accumulated tuples. -/
  relations : Std.HashMap String (Array String × Array JsonTuple) := {}
  /-- Expression pointer → atom ID, for cycle detection. -/
  seen : Std.HashMap UInt64 String := {}
  nextId : Nat := 0

/-- Generate a fresh atom ID. -/
def WalkState.freshId (s : WalkState) : String × WalkState :=
  let id := s!"atom_{s.nextId}"
  (id, { s with nextId := s.nextId + 1 })

/-- Register an atom in the state. -/
def WalkState.addAtom (s : WalkState) (atom : JsonAtom) : WalkState :=
  { s with atoms := s.atoms.push atom }

/-- Add a tuple to a relation, creating the relation if needed. -/
def WalkState.addTuple (s : WalkState) (relName : String) (types : Array String)
    (tuple : JsonTuple) : WalkState :=
  let existing := s.relations.getD relName (types, #[])
  { s with relations := s.relations.insert relName (existing.1, existing.2.push tuple) }

/-- Mark an expression as seen with the given atom ID. -/
def WalkState.markSeen (s : WalkState) (hash : UInt64) (atomId : String) : WalkState :=
  { s with seen := s.seen.insert hash atomId }

/-- Mark an already-emitted atom as DAG-shared (visited from more than one
    parent). Finds the atom by id in `atoms` and sets its `shared` flag. -/
def WalkState.markShared (s : WalkState) (atomId : String) : WalkState :=
  { s with atoms := s.atoms.map fun a => if a.id == atomId then { a with shared := true } else a }

/-- Convert accumulated state to a JsonDataInstance. -/
def WalkState.toDataInstance (s : WalkState) : JsonDataInstance :=
  let relations := s.relations.toArray.map fun (name, types, tuples) =>
    { id := name, name := name, types := types, tuples := tuples : JsonRelation }
  { atoms := s.atoms, relations := relations }

/-- Configuration for the expression walker. -/
structure WalkConfig where
  /-- When true, skip Prop-typed fields (data mode). When false, show them (proof mode). -/
  filterProofs : Bool := true

/-- Check if an expression is a proof or type (erased at runtime). -/
def isProofArg (e : Expr) : MetaM Bool := do
  let ty ← inferType e
  -- Use Meta.isProp for proper sort-level check (handles ∀-typed proofs)
  let isProp ← Meta.isProp ty
  return isProp || ty.isSort

/-- Get the short name from a fully qualified Lean name. -/
def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => "_"

/-- Pretty-print an expression concisely for use as a label. -/
def ppLabel (e : Expr) : MetaM String := do
  let fmt ← ppExpr e
  return toString fmt

/-- A custom relationalizer function.
    Receives the expression to decompose and the default walker for recursion. -/
def CustomRelationalizer :=
  Expr → (Expr → StateT WalkState MetaM String) → StateT WalkState MetaM String

/-- Runtime registry of custom relationalizers, keyed by type name. -/
initialize spytialRelationalizerRegistry :
    IO.Ref (Std.HashMap Name CustomRelationalizer) ← IO.mkRef {}

/-- Look up a custom relationalizer for a type name. -/
def getSpytialRelationalizer? (typeName : Name) : IO (Option CustomRelationalizer) := do
  let map ← spytialRelationalizerRegistry.get
  return map.get? typeName

/-- Register a custom relationalizer for a type. -/
def registerSpytialRelationalizer (typeName : Name) (fn : CustomRelationalizer) : IO Unit :=
  spytialRelationalizerRegistry.modify fun m => m.insert typeName fn

/-- Try to enumerate all elements of a finite type.
    Returns `some [(label, expr)]` for finite types, `none` otherwise. -/
def tryEnumerateDomain (ty : Expr) : MetaM (Option (Array (String × Expr))) := do
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

/-- Walk a Lean expression and produce atoms + relations.
    Returns the atom ID assigned to this expression. -/
partial def walkExpr (cfg : WalkConfig := {}) (eOrig : Expr) : StateT WalkState MetaM String := do
  -- Save original name before WHNF unfolds it
  let origName := eOrig.getAppFn.constName?
  -- WHNF reduce to expose constructors
  let e ← Meta.whnf eOrig

  -- Check for cycles / DAG sharing
  let hash := e.hash
  let s ← get
  if let some existingId := s.seen[hash]? then
    -- Revisiting a structurally identical subterm: mark the already-emitted
    -- atom as shared so downstream consumers can style it distinctly.
    modify fun s => s.markShared existingId
    return existingId

  let ty ← Meta.inferType e

  -- Allocate a fresh ID and mark as seen immediately (before recursing)
  let s ← get
  let (atomId, s) := s.freshId
  let s := s.markSeen hash atomId
  set s

  -- Check for custom relationalizer before default dispatch
  let tyWhnfForLookup ← Meta.whnf ty
  if let .const typeConstName _ := tyWhnfForLookup.getAppFn then
    if let some relFn ← getSpytialRelationalizer? typeConstName then
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
    let typeName ← do
      let tyWhnf ← Meta.whnf ty
      match tyWhnf.getAppFn with
      | .const n _ => pure (shortName n)
      | _ => pure (← ppLabel ty)
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
    -- Try to get the type name (keep the whnf'd type around for index reading)
    let tyWhnf ← Meta.whnf ty
    let typeName ← do
      match tyWhnf.getAppFn with
      | .const n _ => pure (shortName n)
      | _ => pure (← ppLabel ty)

    -- Check if it's an application of a constructor
    match e.getAppFn with
    | .const fnName _ => do
      let env ← getEnv
      -- Quotient values: `Quot.mk r repr` is kernel-primitive (`.quotInfo`,
      -- not `.ctorInfo`), so it misses the constructor check below and would
      -- otherwise become an opaque leaf. We special-case it: emit a `⟦·⟧`
      -- atom and walk the representative (the last argument) via a `repr` edge.
      -- `Quotient.mk` / `Quotient.mk'` usually reduce to `Quot.mk` under whnf,
      -- but we match those const heads too in case whnf stopped early.
      if fnName == ``Quot.mk || fnName == ``Quotient.mk || fnName == ``Quotient.mk' then
        let args := e.getAppArgs
        modify fun s => s.addAtom { id := atomId, type := typeName, label := "⟦·⟧" }
        -- A full application has ≥ 3 args; the representative is the last one.
        if args.size ≥ 3 then
          let repr := args[args.size - 1]!
          let childId ← walkExpr cfg repr
          modify fun s => s.addTuple "repr" #[typeName, typeName]
            { atoms := #[atomId, childId], types := #[typeName, typeName] }
        return atomId
      -- Is it a constructor?
      else if let some (.ctorInfo ci) := env.find? fnName then
        let ctorShortName := shortName fnName
        -- Indexed inductive families: surface the index expressions in the
        -- label (e.g. `cons : Vec 2`) so atoms at different indices are
        -- distinguishable. The `type` field stays the head const short name —
        -- selectors depend on it, so only the *label* changes, and only when
        -- the family actually has indices.
        let label ← do
          let indVal? := env.find? ci.induct
          match indVal? with
          | some (.inductInfo iv) =>
            if iv.numIndices > 0 then
              -- The value's type is `T params… indices…`; read the trailing
              -- `numIndices` arguments off the (already whnf'd) type.
              let tyArgs := tyWhnf.getAppArgs
              let indexExprs := tyArgs.extract (tyArgs.size - iv.numIndices) tyArgs.size
              let mut indexStrs : Array String := #[]
              for ix in indexExprs do
                -- Reduce the index to a normal form so e.g. `n + 1` with a
                -- literal `n` prints as `2`, not `1 + 1`.
                let ixR ← Meta.whnf ix
                indexStrs := indexStrs.push (← ppLabel ixR)
              let joined := String.intercalate " " indexStrs.toList
              pure s!"{ctorShortName} : {typeName} {joined}"
            else
              pure ctorShortName
          | _ => pure ctorShortName
        modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
        -- Extract binder names from the constructor type (skip type params)
        let mut binderNames : Array Name := #[]
        let mut ctorTy := ci.type
        let mut paramIdx := 0
        while ctorTy.isForall do
          if paramIdx >= ci.numParams then
            binderNames := binderNames.push ctorTy.bindingName!
          paramIdx := paramIdx + 1
          ctorTy := ctorTy.bindingBody!
        -- Process data arguments (skip type and proof parameters)
        let args := e.getAppArgs
        let numParams := ci.numParams
        let dataArgs := args.extract numParams args.size
        for i in [:dataArgs.size] do
          let arg := dataArgs[i]!
          let isProof ← if cfg.filterProofs then isProofArg arg else pure false
          unless isProof do
            let childId ← walkExpr cfg arg
            -- Use the binder name if available, otherwise fall back to index
            let fieldName :=
              if h : i < binderNames.size then
                let n := binderNames[i]
                if n.isAnonymous then s!"{ctorShortName}_{i}"
                else toString n
              else s!"{ctorShortName}_{i}"
            modify fun s => s.addTuple fieldName #[typeName, typeName]
              { atoms := #[atomId, childId], types := #[typeName, typeName] }
        return atomId
      -- Is it a structure projection?
      else if isStructure env (← do
            let tyFn := (← Meta.whnf ty).getAppFn
            match tyFn with
            | .const n _ => pure n
            | _ => pure .anonymous) then
        -- Walk all structure fields
        let tyConst := match (← Meta.whnf ty).getAppFn with
          | .const n _ => n
          | _ => .anonymous
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
def relationalize (e : Expr) (cfg : WalkConfig := {}) : MetaM JsonDataInstance := do
  let (_, state) ← walkExpr cfg e |>.run {}
  return state.toDataInstance

end SpytialLean

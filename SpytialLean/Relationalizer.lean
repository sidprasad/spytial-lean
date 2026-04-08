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

/-- Convert accumulated state to a JsonDataInstance. -/
def WalkState.toDataInstance (s : WalkState) : JsonDataInstance :=
  let relations := s.relations.toArray.map fun (name, types, tuples) =>
    { id := name, name := name, types := types, tuples := tuples : JsonRelation }
  { atoms := s.atoms, relations := relations }

/-- Check if a type is a proposition (erased at runtime). -/
def isProofArg (e : Expr) : MetaM Bool := do
  let ty ← inferType e
  return ty.isProp || ty.isSort

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

/-- Walk a Lean expression and produce atoms + relations.
    Returns the atom ID assigned to this expression. -/
partial def walkExpr (e : Expr) : StateT WalkState MetaM String := do
  -- WHNF reduce to expose constructors
  let e ← Meta.whnf e

  -- Check for cycles
  let hash := e.hash
  let s ← get
  if let some existingId := s.seen[hash]? then
    return existingId

  let ty ← Meta.inferType e

  -- Allocate a fresh ID and mark as seen immediately (before recursing)
  let s ← get
  let (atomId, s) := s.freshId
  let s := s.markSeen hash atomId
  set s

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

  | _ => do
    -- Try to get the type name
    let typeName ← do
      let tyWhnf ← Meta.whnf ty
      match tyWhnf.getAppFn with
      | .const n _ => pure (shortName n)
      | _ => pure (← ppLabel ty)

    -- Check if it's an application of a constructor
    match e.getAppFn with
    | .const fnName _ => do
      let env ← getEnv
      -- Is it a constructor?
      if let some (.ctorInfo ci) := env.find? fnName then
        let ctorShortName := shortName fnName
        modify fun s => s.addAtom { id := atomId, type := typeName, label := ctorShortName }
        -- Process data arguments (skip type and proof parameters)
        let args := e.getAppArgs
        let numParams := ci.numParams
        -- Arguments after the type parameters are the data fields
        let dataArgs := args.extract numParams args.size
        for i in [:dataArgs.size] do
          let arg := dataArgs[i]!
          let isProof ← isProofArg arg
          unless isProof do
            let childId ← walkExpr arg
            -- Determine field name from constructor parameter names if available
            let fieldName := s!"{ctorShortName}_{i}"
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
          let projReduced ← Meta.whnf proj
          let childId ← walkExpr projReduced
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
def relationalize (e : Expr) : MetaM JsonDataInstance := do
  let (_, state) ← walkExpr e |>.run {}
  return state.toDataInstance

end SpytialLean

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
  /-- Type-head short names whose values should be collapsed to a single atom
      labeled with their surface notation, instead of being decomposed. Populated
      from `.notationLabel` spec ops (see `SpytialSpec.collapseTypes`). E.g.
      `["List"]` renders `[1, 2, 3]` as one atom rather than a cons chain. -/
  collapseTypes : List String := []
  /-- Hard upper bound on the number of atoms a single walk may produce.
      Relationalizing a very large term (a long `List`, a deeply unfolded proof)
      can generate thousands of atoms, which hangs the widget's layout step and
      is rarely legible anyway. When the count would exceed this limit the walker
      throws a clear error instead of running away. Default 5000 is far above any
      term that renders usefully; raise it deliberately if you really need to. -/
  maxAtoms : Nat := 5000

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

/-- Weak-head normalize a function body just enough to expose its top-level
    structure (`ite` / `dite` / matcher / `casesOn` / `letE`), WITHOUT unfolding
    definitions (so notation like `n * 2` survives) and WITHOUT zeta-reducing
    `let`s (so `letE` stays visible to surface as a `let` node). -/
def whnfBody (e : Expr) : MetaM Expr :=
  Meta.withConfig (fun c => { c with zeta := false, zetaDelta := false })
    (Meta.whnfCore e)

/-- Short name of a type's head constant (whnf'd), or its pretty-printed form
    if the head is not a constant. Used to fill the `type` field of atoms. -/
def typeShortName (ty : Expr) : MetaM String := do
  match (← Meta.whnf ty).getAppFn with
  | .const n _ => pure (shortName n)
  | _ => pure (← ppLabel ty)

/-- The data needed to decompose a `T.casesOn` application: the inductive's
    parameter / index counts and its constructors in declaration order. -/
structure CasesOnInfo where
  numParams : Nat
  numIndices : Nat
  ctors : Array Name

/-- Allocate a fresh atom id, enforcing `cfg.maxAtoms`.

    Every atom-producing path runs through one of the `freshId` call sites, so
    routing them all through this helper makes `maxAtoms` a hard cap on the total
    atom count regardless of which walker (value, function body, matcher, …)
    produced them. When the next id would push the count over the limit it throws
    an actionable error instead of building a runaway diagram. The error text is
    deterministic (it does not depend on hash ordering). -/
def freshAtomId (cfg : WalkConfig) : StateT WalkState MetaM String := do
  let s ← get
  let (atomId, s) := s.freshId
  if s.nextId > cfg.maxAtoms then
    throwError "spytial: relationalize produced over {cfg.maxAtoms} atoms \
      (the WalkConfig.maxAtoms limit was hit); the term is too large to \
      visualize usefully. Increase the limit via WalkConfig.maxAtoms, or \
      visualize a smaller sub-term."
  set s
  return atomId

/-- Emit a single leaf atom for an already-reduced expression and return its id.

    Pretty-prints `e` *as given* (no further reduction). The structural walker
    uses this for leaves of a function body so that arithmetic on the bound
    variable keeps its surface form (`n * 2`) instead of being unfolded by the
    full `whnf` that `walkExpr` would apply at its entry. -/
def emitLeaf (cfg : WalkConfig := {}) (e : Expr) : StateT WalkState MetaM String := do
  let atomId ← freshAtomId cfg
  let typeName ← typeShortName (← Meta.inferType e)
  let label ← ppLabel e
  modify fun s => s.addAtom { id := atomId, type := typeName, label := label }
  return atomId

/-- If `fnName` is `T.casesOn` for an inductive `T`, return the `CasesOnInfo`
    describing `T`; otherwise `none`. The name must be `Name.str indName "casesOn"`
    where `indName` resolves to an `InductiveVal`. -/
def isCasesOnApp? (fnName : Name) : MetaM (Option CasesOnInfo) := do
  match fnName with
  | .str indName "casesOn" =>
    match (← getEnv).find? indName with
    | some (.inductInfo iv) =>
      return some { numParams := iv.numParams, numIndices := iv.numIndices,
                    ctors := iv.ctors.toArray }
    | _ => return none
  | _ => return none

mutual

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

  -- Allocate a fresh ID (enforcing `maxAtoms`) and mark as seen immediately
  -- (before recursing). This is the single chokepoint every `walkExpr`-entry
  -- atom flows through; `emitLeaf` and the structural walkers below allocate
  -- via `freshAtomId` too, so the cap bounds the total regardless of path.
  let atomId ← freshAtomId cfg
  modify fun s => s.markSeen hash atomId

  -- Notation collapse: if this value's type-head short name was opted in via a
  -- `.notationLabel` spec op, emit ONE atom labeled with the surface notation of
  -- the *original* (pre-whnf) expression and stop. `eOrig` is what the delaborator
  -- resugars (so `[1, 2, 3]` survives instead of the cons chain). This runs before
  -- the custom-relationalizer dispatch and the main match so neither decomposes it.
  let tyWhnfForLookup ← Meta.whnf ty
  let typeHeadShortName : Option String := match tyWhnfForLookup.getAppFn with
    | .const n _ => some (shortName n)
    | _ => none
  if let some tn := typeHeadShortName then
    if cfg.collapseTypes.contains tn then
      let label ← ppLabel eOrig
      modify fun s => s.addAtom { id := atomId, type := tn, label := label }
      return atomId

  -- Check for custom relationalizer before default dispatch
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

  -- Lambda — try to enumerate finite domain (extensional view, what it
  -- computes); otherwise decompose the body structurally (intensional view,
  -- how it is defined) instead of leaving an opaque leaf.
  | .lam binderName binderType body bi => do
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
      -- Extensional view: enumerate input→output edges. This is the default
      -- for enumerable domains and its output shape must not change.
      for (elemLabel, elemExpr) in elems do
        let result ← Meta.whnf (Expr.app e elemExpr)
        let childId ← walkExpr cfg result
        modify fun s => s.addTuple elemLabel #[typeName, typeName]
          { atoms := #[atomId, childId], types := #[typeName, typeName] }
    | none =>
      -- Non-finite domain: decompose the body structurally. Enter the binder
      -- so the bound variable is a free variable in scope, then walk the body
      -- through the structural walker. All walking happens INSIDE the
      -- `withLocalDecl` continuation so `ppExpr`/`inferType` on subterms
      -- containing the fvar succeed.
      Meta.withLocalDecl binderName bi binderType fun fv => do
        let bodyExpr := body.instantiate1 fv
        let childId ← walkBody cfg bodyExpr
        modify fun s => s.addTuple "body" #[typeName, typeName]
          { atoms := #[atomId, childId], types := #[typeName, typeName] }
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

/-- Structurally decompose a function body (intensional view).

    Used by the non-finite path of `walkExpr`'s `.lam` arm. `whnfBody`-reduces
    the expression (weak-head, no definition unfolding, no `let` zeta) and
    dispatches on its shape:

    - `ite` / `dite` applications → a node labeled `if` with `condition` /
      `then` / `else` edges (`dite` branches are lambdas over the decidability
      proof; their bodies are decomposed through `walkBodyLam`).
    - matcher auxiliaries (`f.match_n`) and `T.casesOn` applications → a node
      labeled `match`, a `match` edge to the discriminant, and one edge per
      branch labeled by the corresponding constructor's short name. Branch
      bodies are lambdas over the constructor fields, decomposed via
      `walkBodyLam` (so nested structure surfaces).
    - `Expr.letE` → a node labeled `let` with `let_value` / `let_body` edges.
    - nested `.lam` → recurse: multi-argument functions decompose one binder at
      a time, the inner lambda reached via a `body` edge from `walkExpr`.

    Anything else (the bound variable itself, applications of it, arithmetic on
    it) falls back to `walkExpr`, which pretty-prints a leaf label like `n * 2`.
    Recursive sub-parts go back through `walkBody`, so nested `if`s nest. -/
partial def walkBody (cfg : WalkConfig := {}) (e : Expr) :
    StateT WalkState MetaM String := do
  -- Detect `T.casesOn` BEFORE reducing: `whnfBody` would unfold it to `T.rec`
  -- (a different, harder-to-read shape). Matchers, `ite`/`dite`, and `letE` all
  -- survive `whnfBody`, so they are handled after reduction below.
  if let .const fnName _ := e.getAppFn then
    if let some info ← isCasesOnApp? fnName then
      return ← walkCasesOn cfg e info e.getAppArgs
  let e ← whnfBody e
  match e.getAppFn with
  | .const fnName _ =>
    let args := e.getAppArgs
    -- if / dite: `@ite α c inst t e` / `@dite α c inst t e` — both have 5 args
    -- with the condition at index 1, the `then` branch at 3, `else` at 4.
    if (fnName == ``ite || fnName == ``dite) && args.size == 5 then
      let isDite := fnName == ``dite
      let ty ← Meta.inferType e
      let typeName ← typeShortName ty
      let atomId ← freshAtomId cfg
      modify fun s => s.addAtom { id := atomId, type := typeName, label := "if" }
      let condId ← walkBody cfg args[1]!
      modify fun s => s.addTuple "condition" #[typeName, typeName]
        { atoms := #[atomId, condId], types := #[typeName, typeName] }
      -- `dite` branches abstract over the proof of `c` (resp. `¬ c`); peel that
      -- binder off and decompose the branch body. `ite` branches are plain.
      let thenId ← if isDite then walkBodyLam cfg args[3]! else walkBody cfg args[3]!
      modify fun s => s.addTuple "then" #[typeName, typeName]
        { atoms := #[atomId, thenId], types := #[typeName, typeName] }
      let elseId ← if isDite then walkBodyLam cfg args[4]! else walkBody cfg args[4]!
      modify fun s => s.addTuple "else" #[typeName, typeName]
        { atoms := #[atomId, elseId], types := #[typeName, typeName] }
      return atomId
    -- Matcher auxiliary (`f.match_n`): a pattern match compiled to a matcher.
    -- Layout of its application args is `[params] [motive] [discrs] [alts]`.
    else if let some mi ← Meta.getMatcherInfo? fnName then
      walkMatch cfg e mi args
    -- `T.casesOn` is normally caught pre-reduction above (whnf unfolds it to
    -- `T.rec`); this is a defensive fallback for any that slips through.
    else if let some info ← isCasesOnApp? fnName then
      walkCasesOn cfg e info args
    else if (← getEnv).find? fnName matches some (.ctorInfo _) then
      -- A constructor application (possibly mentioning the bound variable, e.g.
      -- `x :: xs`): let `walkExpr` decompose it into its fields as usual.
      walkExpr cfg e
    else
      -- Other const application on the bound variable (arithmetic, comparisons,
      -- a recursive call): emit a leaf from the surface form. Going through
      -- `walkExpr` here would full-`whnf` and unfold e.g. `n * 2` into
      -- `(n.mul 1).add n`; `emitLeaf` keeps the readable `n * 2`.
      emitLeaf cfg e
  | .letE declName declType value body _nonDep =>
    -- Surface a `let`: walk the bound value, then the body with the let
    -- variable in scope as a local decl.
    let ty ← Meta.inferType e
    let typeName ← typeShortName ty
    let atomId ← freshAtomId cfg
    modify fun s => s.addAtom { id := atomId, type := typeName, label := s!"let {declName}" }
    let valId ← walkBody cfg value
    modify fun s => s.addTuple "let_value" #[typeName, typeName]
      { atoms := #[atomId, valId], types := #[typeName, typeName] }
    Meta.withLetDecl declName declType value fun fv => do
      let bodyExpr := body.instantiate1 fv
      let bodyId ← walkBody cfg bodyExpr
      modify fun s => s.addTuple "let_body" #[typeName, typeName]
        { atoms := #[atomId, bodyId], types := #[typeName, typeName] }
    return atomId
  | .lam .. =>
    -- Nested lambda (multi-argument function). Hand back to `walkExpr`, whose
    -- `.lam` arm emits the lambda atom and recurses into its body via a `body`
    -- edge — so each binder becomes its own layer.
    walkExpr cfg e
  | .lit _ =>
    -- A bare literal: `walkExpr` already renders these cleanly (and `whnf` is
    -- harmless on literals).
    walkExpr cfg e
  | _ =>
    -- Bound variable, projection, or any other non-application head: emit a
    -- leaf from the surface form (e.g. the binder name `n`, or `n.fst`).
    emitLeaf cfg e

/-- Decompose a branch lambda: peel its binders (constructor fields, or a
    `dite` decidability proof), introducing a fresh local for each, then walk
    the resulting body structurally. Used for matcher/`casesOn` alternatives and
    `dite` branches, whose bodies are lambdas we want to see *through* rather
    than render as `λ`-leaves. -/
partial def walkBodyLam (cfg : WalkConfig := {}) (e : Expr) :
    StateT WalkState MetaM String := do
  let e ← whnfBody e
  match e with
  | .lam binderName binderType lamBody bi =>
    Meta.withLocalDecl binderName bi binderType fun fv => do
      walkBodyLam cfg (lamBody.instantiate1 fv)
  | _ => walkBody cfg e

/-- Decompose a matcher application into a `match` node: an edge `match` to the
    walked discriminant and one edge per alternative, labeled by the matching
    constructor's short name. `mi` is the matcher's `MatcherInfo`; `args` are the
    full application arguments laid out as `[params] [motive] [discrs] [alts]`. -/
partial def walkMatch (cfg : WalkConfig := {}) (e : Expr)
    (mi : Lean.Meta.MatcherInfo) (args : Array Expr) :
    StateT WalkState MetaM String := do
  let ty ← Meta.inferType e
  let typeName ← typeShortName ty
  let atomId ← freshAtomId cfg
  modify fun s => s.addAtom { id := atomId, type := typeName, label := "match" }
  -- Discriminants sit right after the motive (one motive slot, then numDiscrs).
  let discrStart := mi.numParams + 1
  let altStart := discrStart + mi.numDiscrs
  -- Walk each discriminant via the standard walker and link it with `match`.
  let discrs := args.extract discrStart altStart
  let mut ctorNames : Array String := #[]
  for discr in discrs do
    let discrId ← walkExpr cfg discr
    modify fun s => s.addTuple "match" #[typeName, typeName]
      { atoms := #[atomId, discrId], types := #[typeName, typeName] }
  -- Constructor order for branch labels comes from the discriminant's
  -- inductive (single-discriminant matches are the common case).
  if mi.numDiscrs == 1 then
    let dty ← Meta.inferType discrs[0]!
    match (← Meta.whnf dty).getAppFn with
    | .const indName _ =>
      if let some (.inductInfo iv) := (← getEnv).find? indName then
        ctorNames := iv.ctors.toArray.map shortName
    | _ => pure ()
  -- One edge per alternative; the branch body is a lambda over its ctor fields.
  let alts := args.extract altStart args.size
  for h : i in [:alts.size] do
    let altId ← walkBodyLam cfg alts[i]
    let edgeName := if h : i < ctorNames.size then ctorNames[i] else s!"case_{i}"
    modify fun s => s.addTuple edgeName #[typeName, typeName]
      { atoms := #[atomId, altId], types := #[typeName, typeName] }
  return atomId

/-- Decompose a `T.casesOn` application into a `match` node, analogous to
    `walkMatch`. Args are `[params] [motive] [indices] [major] [alts]`; `info`
    carries the inductive's `numParams` / `numIndices` and the ctor order. -/
partial def walkCasesOn (cfg : WalkConfig := {}) (e : Expr)
    (info : CasesOnInfo) (args : Array Expr) :
    StateT WalkState MetaM String := do
  let ty ← Meta.inferType e
  let typeName ← typeShortName ty
  let atomId ← freshAtomId cfg
  modify fun s => s.addAtom { id := atomId, type := typeName, label := "match" }
  -- Major (the scrutinee) sits after params, motive, and indices.
  let majorPos := info.numParams + 1 + info.numIndices
  if h : majorPos < args.size then
    let majorId ← walkExpr cfg args[majorPos]
    modify fun s => s.addTuple "match" #[typeName, typeName]
      { atoms := #[atomId, majorId], types := #[typeName, typeName] }
  -- Branches follow the major, one per constructor in declaration order.
  let altStart := majorPos + 1
  let alts := args.extract altStart args.size
  let ctorNames := info.ctors.map shortName
  for h : i in [:alts.size] do
    let altId ← walkBodyLam cfg alts[i]
    let edgeName := if h : i < ctorNames.size then ctorNames[i] else s!"case_{i}"
    modify fun s => s.addTuple edgeName #[typeName, typeName]
      { atoms := #[atomId, altId], types := #[typeName, typeName] }
  return atomId

end

/-- Walk an expression and produce a complete JsonDataInstance. -/
def relationalize (e : Expr) (cfg : WalkConfig := {}) : MetaM JsonDataInstance := do
  let (_, state) ← walkExpr cfg e |>.run {}
  return state.toDataInstance

/-- Walk every expression in `es` through a *single shared* `WalkState`, then
    produce one combined `JsonDataInstance`.

    Folding `walkExpr` over a single state (rather than relationalizing each
    expression independently and merging) means the per-expr `seen` cache is
    shared: structurally identical subterms across the whole population collapse
    to the same atom id, so e.g. a function field pointing at an enumerated
    element unifies with that element. Used by `#spytial.enumerate` to render all
    inhabitants of a finite type in one diagram. -/
def relationalizeAll (es : Array Expr) (cfg : WalkConfig := {}) : MetaM JsonDataInstance := do
  let walkAll : StateT WalkState MetaM Unit := do
    for e in es do
      let _ ← walkExpr cfg e
  let (_, state) ← walkAll.run {}
  return state.toDataInstance

end SpytialLean

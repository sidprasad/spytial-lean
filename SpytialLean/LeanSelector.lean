module

public import Lean
public meta import SpytialLean.Types
public meta import SpytialLean.Selector
public meta import SpytialLean.Spec
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.Sel

namespace SpytialLean

open Lean Meta

/-! # Resolving embedded Lean selectors

Each selector becomes one term over arrays of the walked values, run through
Lean's compiled evaluator. The term reports index tuples, and an index into a
column array *is* an atom. A predicate over symbolic values instead runs
through the retained evidence: direct proof matching, then bounded
simplification; a missing proof is not a proof of the negation. -/

public section

meta def maxSelArity : Nat := 4

meta inductive LeanRelShape where
  | pred (isProp : Bool)
  | sel (T : Expr)
  deriving Inhabited

/-- For `.sel` the columns of the selected tuple, for `.pred` the arguments. -/
meta structure LeanRelKind where
  domains : Array Expr
  shape : LeanRelShape
  deriving Inhabited

meta def LeanRelKind.arity (k : LeanRelKind) : Nat := k.domains.size

/-- `Sel.lean` spells `selIdx1..maxSelArity` and `locate1..maxSelArity` by hand;
    the arity checks below keep `n` inside that range. -/
private meta def rung (stem : Name) (n : Nat) : Name := stem.appendAfter (toString n)

/-- Reducible normalization at each level, so an `abbrev` standing for a
    product contributes its own columns rather than reading as one. -/
private meta partial def splitProds (α : Expr) : MetaM (Array Expr) := do
  let α ← whnfR α
  if α.isAppOfArity ``Prod 2 then
    return #[α.getAppArgs[0]!] ++ (← splitProds α.getAppArgs[1]!)
  else
    return #[α]

/-- Shared by the elaborator, which needs the arity to check the op position,
    and by resolution, so the two cannot drift. -/
meta def classifyLeanRel (fn : Expr) : MetaM LeanRelKind := do
  let ty ← whnfR (← instantiateMVars (← inferType fn))
  if ty.getAppFn.isConstOf ``Spytial.Sel then
    if let #[T, α] := ty.getAppArgs then
      let cols ← splitProds α
      if cols.size > maxSelArity then
        throwError "a Lean selector can select at most {maxSelArity}-tuples, \
          but this one selects {cols.size}-tuples"
      return { domains := cols, shape := .sel T }
  let mut domains := #[]
  let mut ty ← whnf ty
  while ty matches .forallE .. do
    let .forallE _ dom body _ := ty | unreachable!
    if body.hasLooseBVars then break
    domains := domains.push (← whnfR dom)
    ty ← whnf body
  if domains.isEmpty then
    throwError "a raw Lean selector must be a function over the walked types, \
      but this term has type {← inferType fn}"
  if ty matches .forallE .. then
    throwError "a raw Lean selector cannot have a dependent argument type; \
      this one has type {← inferType fn}"
  let checkArity (n : Nat) : MetaM Unit := do
    if n > maxSelArity then
      throwError "a Lean selector can select at most {maxSelArity}-tuples, \
        but this one selects {n}-tuples"
  match ty with
  | .sort .zero =>
    checkArity domains.size
    return { domains, shape := .pred true }
  | _ =>
    if ty.isConstOf ``Bool then
      checkArity domains.size
      return { domains, shape := .pred false }
    throwError "a raw Lean selector returns `Bool` or `Prop` — the walked \
      tuples it accepts; to select computed values, write a `Spytial.Sel`"

meta def boolifyPred (fn : Expr) (doms : Array Expr) : MetaM Expr := do
  let rec go (i : Nat) (xs : Array Expr) : MetaM Expr := do
    if h : i < doms.size then
      withLocalDeclD (Name.mkSimple s!"x{i}") doms[i] fun x =>
        go (i + 1) (xs.push x)
    else
      let prop := (mkAppN fn xs).headBeta
      -- `decide`'s instance argument trails the proposition, so `mkAppM` would
      -- leave it unapplied. Instance search does not unfold a named predicate,
      -- so expose the proposition first.
      let inst ← try synthInstance (← mkAppM ``Decidable #[← whnf prop])
        catch _ => throwError "the proposition{indentExpr prop}\nneeds a \
          `Decidable` instance to run as a selector"
      mkLambdaFVars xs (mkApp2 (mkConst ``decide) prop inst)
  go 0 #[]

private meta def maxSelectedTuples : Nat := 4096

/-- Bounded before evaluation: the enumeration runs even when nothing is
    selected. -/
private meta def maxEnumeratedPoints : Nat := 1000000

meta structure LeanSelCtx where
  datum : Expr
  di : JsonDataInstance
  prov : Provenance
  evidence : SelectorEvidence := {}

/-- The walker's sig is a short name, so the definitional check is what keeps a
    same-named type's atoms out of the array, which would otherwise make the
    evaluated term ill-typed. An open subterm has no value to run on and stays
    out too. -/
meta def LeanSelCtx.columnFor (ctx : LeanSelCtx) (σ : Expr) :
    MetaM (Array String × Array Expr) := do
  let sig ← sigOfType σ
  let mut ids := #[]
  let mut es := #[]
  for a in ctx.di.atoms do
    if a.type == sig then
      if let some e := ctx.prov[a.id]? then
        if isClosedValue e then
          if ← withNewMCtxDepth (isDefEq (← inferType e) σ) then
            ids := ids.push a.id
            es := es.push e
  return (ids, es)

private meta def listListNatTy : Expr :=
  mkApp (mkConst ``List [.zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))

private meta unsafe def evalIdxTuplesUnsafe (e : Expr) : MetaM (List (List Nat)) :=
  Meta.evalExpr (List (List Nat)) listListNatTy e

@[implemented_by evalIdxTuplesUnsafe]
private meta opaque evalIdxTuplesCore (e : Expr) : MetaM (List (List Nat))

private meta def evalIdxTuples (e : Expr) : MetaM (List (List Nat)) := do
  try evalIdxTuplesCore e
  catch ex => throwError "the raw Lean selector failed to run: {ex.toMessageData}"

/-- An inherited spec composes into a child render, so a parent's `Sel` must
    apply to the child's parent part. -/
private meta def coerceToParent? (datum datumTy T : Expr) : MetaM (Option Expr) := do
  let .const dn _ := (← whnfR datumTy).getAppFn | return none
  let .const tn _ := (← whnfR T).getAppFn | return none
  let some path := getPathToBaseStructure? (← getEnv) tn dn | return none
  try
    let e ← path.foldlM (fun acc proj => mkAppM proj #[acc]) datum
    -- The parameters must line up too: `Sel (P Nat)` does not fit a `C Bool`.
    if ← withNewMCtxDepth (isDefEq (← inferType e) T) then return some e
    return none
  catch _ => return none

/-- The selected tuples, as arrays of atom ids. -/
private meta def evalCompiledRel (ctx : LeanSelCtx) (fn : Expr)
    (columns? : Option (Array (Array String × Array Expr)) := none) :
    MetaM (Array (Array String)) := do
  let kind ← classifyLeanRel fn
  let cols ← columns?.getDM (kind.domains.mapM ctx.columnFor)
  let us ← (cols.zip kind.domains).mapM fun ((_, es), σ) => mkArrayLit σ es.toList
  let term ← match kind.shape with
    | .pred isProp =>
      let points := cols.foldl (fun n (ids, _) => n * ids.size) 1
      if points > maxEnumeratedPoints then
        throwError "this predicate would be decided at {points} points (the \
          product of its column sizes), over the limit of \
          {maxEnumeratedPoints}; write a `Spytial.Sel` that computes its \
          tuples instead"
      let p ← if isProp then boolifyPred fn kind.domains else pure fn
      mkAppM (rung `Spytial.Sel.selIdx kind.domains.size) (us.push p)
    | .sel T =>
      unless isClosedValue ctx.datum do
        throwError "a `Spytial.Sel` runs on the whole value being drawn, but \
          the context does not determine that value; a predicate selects \
          among the individually known values instead"
      let datumTy ← inferType ctx.datum
      let datum ← do
        if ← withNewMCtxDepth (isDefEq datumTy T) then pure ctx.datum
        else if let some d ← coerceToParent? ctx.datum datumTy T then pure d
        else throwError "this selector expects a value of type {T}, but the \
          value being drawn has type {datumTy}"
      let body ← mkAppM ``Spytial.Sel.select #[fn, datum]
      try mkAppM (rung `Spytial.Sel.locate kind.domains.size) (us.push body)
      catch ex => throwError "{ex.toMessageData}\n\nthis selector returns \
        values, and a returned value is located by `==` — add `deriving BEq` \
        to the returned type"
  let tuples ← evalIdxTuples term
  -- Indexes are minted in walk order, so sorting them sorts the rendered
  -- selector into walk order; the dedup reads the list as a set.
  let mut out : Array (Array String) := #[]
  let mut prev? : Option (List Nat) := none
  for t in tuples.toArray.qsort (·.lex ·) do
    if prev? == some t then continue
    prev? := some t
    let ids := (t.toArray.zip cols).filterMap fun (i, (colIds, _)) => colIds[i]?
    if ids.size == t.length then
      out := out.push ids
  if out.size > maxSelectedTuples then
    throwError "raw Lean selector selects {out.size} tuples, over the \
      limit of {maxSelectedTuples}; a diagram op over that many tuples would \
      not render legibly"
  return out

/-! ## Predicates over the represented datum -/

meta structure PredicateEvidence where
  facts : Array (Expr × Expr)
  simpContext : Simp.Context
  simprocs : Simp.SimprocsArray

private meta def checkPredicateProof (proposition proof : Expr) : MetaM Expr := do
  let proof ← instantiateMVars proof
  let checked := mkApp2 (mkConst ``id [.zero]) proposition proof
  if checked.hasExprMVar || checked.hasLevelMVar || checked.hasSorry then
    throwError "Lean selector evidence contains unresolved holes or sorry"
  match Kernel.check (← getEnv) (← getLCtx) checked with
  | .error exception => throwError "{exception.toMessageData (← getOptions)}"
  | .ok _ => return proof

private meta def preparePredicateEvidence (evidence : SelectorEvidence) :
    MetaM PredicateEvidence := do
  let mut theorems ← getSimpTheorems
  let mut facts := #[]
  for proof in evidence.proofs do
    let proof ← instantiateMVars proof
    -- A hole is not evidence and must never be solved as a side effect.
    if proof.hasExprMVar || proof.hasLevelMVar || proof.hasSorry then continue
    let proposition ← instantiateMVars (← inferType proof)
    unless ← isProp proposition do continue
    let proof ← checkPredicateProof proposition proof
    facts := facts.push (proposition, proof)
    theorems ← theorems.add (.other (.num `spytial.selector facts.size)) #[] proof
  let simpContext ← Simp.mkContext
    (config := { maxSteps := 1000, autoUnfold := true })
    (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
  return { facts, simpContext, simprocs := #[(← Simp.getSimprocs)] }

/-- Establish a proposition without assigning any of the inspected holes.
    Failure to establish it is not evidence for its negation. -/
private meta def provePredicate? (evidence : PredicateEvidence) (proposition : Expr) :
    MetaM (Option Expr) := withoutModifyingState <| withNewMCtxDepth do
  for (fact, proof) in evidence.facts do
    if ← isDefEq proposition fact then
      return some (← checkPredicateProof proposition proof)
  -- A named predicate need not be a simp lemma. Expose its outer proposition;
  -- the simplifier then computes/re-writes the relevant applications inside it.
  let normalized ← whnf proposition
  let (result, _) ← simp normalized evidence.simpContext evidence.simprocs
  unless result.expr.isConstOf ``True do return none
  let proof ← mkOfEqTrue (← result.getProof' normalized)
  return some (← checkPredicateProof proposition proof)

/-- Candidates come only from represented atoms with correctly typed Lean
    terms. Aliases must denote the representative value: a coarser identity
    classifier is not a proof of Lean equality. -/
private meta def predicateColumn (ctx : LeanSelCtx) (evidence : PredicateEvidence)
    (domain : Expr) : MetaM (Array (String × Expr)) := do
  let mut column := #[]
  for atom in ctx.di.atoms do
    let mut candidates := #[]
    if let some term := ctx.prov[atom.id]? then candidates := candidates.push term
    for (term, id) in ctx.evidence.terms do
      if id == atom.id && !candidates.any (·.equal term) then
        candidates := candidates.push term
    let mut representative? := none
    for term in candidates do
      let term ← instantiateMVars term
      if term.hasExprMVar || term.hasLevelMVar || term.hasSorry then continue
      unless ← withoutModifyingState <| withNewMCtxDepth <|
          isDefEq (← inferType term) domain do continue
      if let some representative := representative? then
        let equal ← withoutModifyingState <| withNewMCtxDepth <| isDefEq term representative
        unless equal do
          unless (← provePredicate? evidence (← mkEq term representative)).isSome do continue
      else
        representative? := some term
      column := column.push (atom.id, term)
  return column

private meta def sortSelected (di : JsonDataInstance) (tuples : Array (Array String)) :
    Array (Array String) := Id.run do
  let order := di.atoms.zipIdx |>.foldl (init := ({} : Std.HashMap String Nat))
    fun indices (atom, index) => indices.insert atom.id index
  return tuples.qsort fun a b => Id.run do
    for (x, y) in a.zip b do
      if order[x]! < order[y]! then return true
      if order[x]! > order[y]! then return false
    return false

/-- Resolve an existing Lean selector against the represented datum. Closed
    evaluation and proof-backed simplification are two ways to establish the
    same predicate, in commands and proof contexts alike. -/
private meta def evalLeanRelPrepared (ctx : LeanSelCtx) (evidence : PredicateEvidence)
    (fn : Expr) : MetaM (Array (Array String)) := do
  let fn ← instantiateMVars fn
  if fn.hasExprMVar || fn.hasLevelMVar then
    throwError "a Lean selector cannot contain unresolved holes"
  let kind ← classifyLeanRel fn
  let .pred isProp := kind.shape | return ← evalCompiledRel ctx fn
  let env ← getEnv
  let executable := fun expression => isClosedValue expression &&
    !expression.getUsedConstants.any (isNoncomputable env ·)
  let compiled ← if executable fn then
    if isProp then
      try
        -- Local and classical Decidable instances are evidence, not necessarily
        -- executable code. They must not force an otherwise symbolic check into #eval.
        pure (executable (← boolifyPred fn kind.domains))
      catch _ => pure false
    else pure true
  else pure false
  let columns ← kind.domains.mapM (predicateColumn ctx evidence)
  -- Include backed custom roots too, not only the legacy value-provenance
  -- table. Each atom contributes one closed representative to compiled code.
  let closedColumns := columns.map fun column =>
    column.foldl (init := (#[], #[])) fun (ids, terms) (id, term) =>
      if executable term && !ids.contains id then (ids.push id, terms.push term)
      else (ids, terms)
  let mut selected := #[]
  if compiled then
    unless closedColumns.any (·.1.isEmpty) do
      selected ← evalCompiledRel ctx fn (some closedColumns)
    if (columns.zip closedColumns).all (fun (column, (ids, _)) =>
        column.all fun (id, _) => ids.contains id) then return selected
  let points := columns.foldl (fun n column => n * column.size) 1
  -- Include direct fact comparisons in the work cap, not just successful matches.
  let comparisons := points * max 1 evidence.facts.size
  if comparisons > maxEnumeratedPoints then
    throwError "this Lean predicate requires {comparisons} candidate/evidence checks, over the \
      limit of {maxEnumeratedPoints}; use a narrower predicate or inspection"
  let rec visit (remaining : List (Array (String × Expr))) (ids : Array String)
      (terms : Array Expr) (selected : Array (Array String)) : MetaM (Array (Array String)) := do
    match remaining with
    | column :: rest =>
      column.foldlM (fun selected (id, term) =>
        visit rest (ids.push id) (terms.push term) selected) selected
    | [] =>
      if selected.contains ids then return selected
      -- Compiled evaluation already decided these tuples, including false ones.
      if compiled && (ids.zip closedColumns).all (fun (id, (closedIds, _)) =>
          closedIds.contains id) then return selected
      let application := (mkAppN fn terms).headBeta
      let proposition ← if isProp then pure application
        else mkEq application (mkConst ``Bool.true)
      if (← provePredicate? evidence proposition).isSome then
        if selected.size >= maxSelectedTuples then
          throwError "a Lean predicate selects more than {maxSelectedTuples} tuples"
        return selected.push ids
      return selected
  return sortSelected ctx.di (← visit columns.toList #[] #[] selected)

/-- Resolve one Lean selector directly. Bulk spec resolution uses the prepared
    variant above so several `lean (...)` leaves share one checked evidence and
    simplifier context. -/
meta def evalLeanRel (ctx : LeanSelCtx) (fn : Expr) : MetaM (Array (Array String)) :=
    withoutModifyingState <| withNewMCtxDepth do
  evalLeanRelPrepared ctx (← preparePredicateEvidence ctx.evidence) fn

/-- Tuples as `` `a1->`a2 + `a3->`a4 ``; product binds tighter than union, so
    neither side needs parentheses. -/
private meta def tupleUnion (tuples : Array (Array String)) : Sel := Id.run do
  let mut out : Option Sel := none
  for ids in tuples do
    let mut tuple : Option Sel := none
    for id in ids do
      let a := Sel.atomLit id
      tuple := some <| match tuple with
        | none => a
        | some t => Sel.op .«product» #[t, a]
    if let some t := tuple then
      out := some <| match out with
        | none => t
        | some o => Sel.op .«union» #[o, t]
  return out.getD .empty

meta partial def Sel.resolveLean (ctx : LeanSelCtx) (evidence : PredicateEvidence) :
    Sel → MetaM Sel
  | .leanRel fn => return tupleUnion (← evalLeanRelPrepared ctx evidence fn)
  | .node c op args =>
    return .node c op (← args.mapM (·.mapExprsM (·.resolveLean ctx evidence)))
  | e@(.sig ..) | e@(.rel ..) | e@(.builtin ..) | e@(.var ..) | e@(.num ..)
  | e@(.str ..) | e@(.ctorLit ..) | e@(.boolLit ..) => return e

private meta partial def FieldVal.resolveLean (ctx : LeanSelCtx) (evidence : PredicateEvidence) :
    FieldVal → MetaM FieldVal
  | .sel s => return .sel (← s.resolveLean ctx evidence)
  | .block fs => return .block (← fs.mapM fun (f, v) => return (f, ← v.resolveLean ctx evidence))
  | v@(.rel ..) | v@(.str ..) | v@(.«enum» ..) | v@(.enums ..) | v@(.num ..)
  | v@(.bool ..) => return v

/-! Callers check these before walking the datum: the walk also asks each type
for a `SpytialIdentity`, which reports when it cannot derive one, and a spec
with no raw Lean selector should not pay for that. -/

meta partial def Sel.hasLeanRel : Sel → Bool
  | .leanRel _ => true
  | .node _ _ args => args.any fun a => a.subExprs.any Sel.hasLeanRel
  | .sig .. | .rel .. | .builtin .. | .var .. | .num .. | .str .. | .ctorLit ..
  | .boolLit .. => false

meta partial def FieldVal.hasLeanRel : FieldVal → Bool
  | .sel s => s.hasLeanRel
  | .block fs => fs.any fun (_, v) => v.hasLeanRel
  | .rel .. | .str .. | .«enum» .. | .enums .. | .num .. | .bool .. => false

meta def SpytialSpec.hasLeanRel (spec : SpytialSpec) : Bool :=
  spec.any fun op => op.fields.any fun (_, v) => v.hasLeanRel

/-- Only the fields are rewritten: an op's stamp stays the user's own text, so
    a conflict report cites what they wrote, not the atom ids it resolved to. -/
meta def resolveLeanSelectors (datum : Expr) (di : JsonDataInstance)
    (prov : Provenance) (spec : SpytialSpec) (evidence : SelectorEvidence := {}) :
    MetaM SpytialSpec := withoutModifyingState <| withNewMCtxDepth do
  unless spec.hasLeanRel do return spec
  let ctx : LeanSelCtx := { datum, di, prov, evidence }
  let prepared ← preparePredicateEvidence evidence
  spec.mapM fun op => return { op with
    fields := ← op.fields.mapM fun (f, v) => return (f, ← v.resolveLean ctx prepared) }

end

end SpytialLean

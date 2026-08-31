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

Both selector styles range over the relationalized datum. A Lean predicate
uses the terms and certified evidence interpreting its atoms, not JSON labels.
Closed predicates on closed values retain the compiled evaluation path.
Symbolic applications use direct evidence and bounded simplification; a
missing proof is not a proof of negation.

Whole-value `Spytial.Sel` programs still execute on a closed root and locate
returned values by `BEq`. Atoms without a Lean interpretation cannot be
selected by a Lean predicate. Identity remains the relationalizer's decision.
-/

public section

/-! ## Classifying the selector term -/

/-- The largest tuple a selector may select. -/
meta def maxSelArity : Nat := 4

/-- How the selector term produces its tuples. -/
meta inductive LeanRelShape where
  /-- `… → Bool` / `… → Prop`; every column is enumerated. -/
  | pred (isProp : Bool)
  /-- The canonical form: the term's type is `Spytial.Sel T α`. -/
  | sel (T : Expr)
  deriving Inhabited

/-- The selector term read as a relation: which types its columns range over,
    and how its tuples are produced. -/
meta structure LeanRelKind where
  /-- For `.sel`, the columns of `α`; for a predicate, the argument types. -/
  domains : Array Expr
  shape : LeanRelShape
  deriving Inhabited

/-- One column per domain, for either shape. -/
meta def LeanRelKind.arity (k : LeanRelKind) : Nat := k.domains.size

/-- The column types of a tuple type: `σ₁ × σ₂ × σ₃` splits right-nested.
    Each level is normalized at reducible transparency first, so an `abbrev`
    standing for a product (`abbrev Edge := Node × Node`) contributes its own
    columns rather than reading as one. A column type is normalized for the
    same reason: the walk knows it under its real name. -/
private meta partial def splitProds (α : Expr) : MetaM (Array Expr) := do
  let α ← whnfR α
  if α.isAppOfArity ``Prod 2 then
    return #[α.getAppArgs[0]!] ++ (← splitProds α.getAppArgs[1]!)
  else
    return #[α]

/-- Read the selector term's type as a relation. Shared by the elaborator
    (which needs the arity to check the op position) and by resolution, so the
    two cannot drift. Throws the user-facing rejections. -/
meta def classifyLeanRel (fn : Expr) : MetaM LeanRelKind := do
  -- The canonical form is marked by its type's head; `Sel` is a structure, so
  -- inference keeps the head visible, and reducible normalization sees through
  -- an `abbrev` standing for one.
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
  -- Peel non-dependent arrows; a dependent one ends the argument list.
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

/-- The `Bool` form of a `Prop`-valued predicate: `fun x₁ … xₙ => decide (p x₁ … xₙ)`.
    Fails loudly when the proposition has no `Decidable` instance. -/
meta def boolifyPred (fn : Expr) (doms : Array Expr) : MetaM Expr := do
  let rec go (i : Nat) (xs : Array Expr) : MetaM Expr := do
    if h : i < doms.size then
      withLocalDeclD (Name.mkSimple s!"x{i}") doms[i] fun x =>
        go (i + 1) (xs.push x)
    else
      let prop := (mkAppN fn xs).headBeta
      -- `decide`'s instance argument trails the proposition, so `mkAppM`
      -- would leave it unapplied; synthesize it directly.
      -- Typeclass search does not unfold an ordinary named predicate on its
      -- own. Expose its proposition before asking for the decision procedure.
      let inst ← try synthInstance (← mkAppM ``Decidable #[← whnf prop])
        catch _ => throwError "the proposition{indentExpr prop}\nneeds a \
          `Decidable` instance to run as a selector"
      mkLambdaFVars xs (mkApp2 (mkConst ``decide) prop inst)
  go 0 #[]

/-! ## Resolution context -/

/-- The number of selected tuples past which the diagram stops being one. -/
private meta def maxSelectedTuples : Nat := 4096

/-- The number of points a predicate may be decided at: the product of its
    column sizes, bounded *before* evaluation, because the enumeration runs
    even when nothing is selected. -/
private meta def maxEnumeratedPoints : Nat := 1000000

/-- What a raw Lean selector resolves against: the datum, the walked instance,
    and the subterm behind each atom. -/
meta structure LeanSelCtx where
  datum : Expr
  di : JsonDataInstance
  prov : Provenance
  evidence : SelectorEvidence := {}

/-- One column: the walked atoms of type `σ`, with the value behind each, in
    atom order. The evaluated term reports indexes into this array, so an
    index *is* an atom. The walker's sig is a short name; the definitional
    type check keeps a same-named type's atoms out of the array, which would
    otherwise make the evaluated term ill-typed. An open subterm (one the
    context leaves symbolic) has no value to run on and stays out too — the
    compiled evaluator could not quote it. -/
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

/-! ## The one evaluation -/

private meta def listListNatTy : Expr :=
  mkApp (mkConst ``List [.zero]) (mkApp (mkConst ``List [.zero]) (mkConst ``Nat))

private meta unsafe def evalIdxTuplesUnsafe (e : Expr) : MetaM (List (List Nat)) :=
  Meta.evalExpr (List (List Nat)) listListNatTy e

@[implemented_by evalIdxTuplesUnsafe]
private meta opaque evalIdxTuplesCore (e : Expr) : MetaM (List (List Nat))

/-- Run the built term through the compiled evaluator. Errors pass through —
    Lean's own message for a missing `meta import` names the fix. -/
private meta def evalIdxTuples (e : Expr) : MetaM (List (List Nat)) := do
  try evalIdxTuplesCore e
  catch ex => throwError "the raw Lean selector failed to run: {ex.toMessageData}"

/-- The datum coerced to `T`, when `T` is a parent structure of its type.
    An inherited spec composes into a child render (`lookupTypeSpec` walks the
    parent chain), so a parent's `Sel` must apply to the child's parent part —
    reached through the projection chain Lean already generates. -/
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

/-! ## Evaluating one selector -/

/-- The tuples the selector term selects on this datum, as arrays of atom ids. -/
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
      let helper := match kind.domains.size with
        | 1 => ``Spytial.Sel.selIdx1
        | 2 => ``Spytial.Sel.selIdx2
        | 3 => ``Spytial.Sel.selIdx3
        | _ => ``Spytial.Sel.selIdx4
      mkAppM helper (us.push p)
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
      let helper := match kind.domains.size with
        | 1 => ``Spytial.Sel.locate1
        | 2 => ``Spytial.Sel.locate2
        | 3 => ``Spytial.Sel.locate3
        | _ => ``Spytial.Sel.locate4
      -- The half of the contract that needs an instance: a returned value is
      -- located by `==`, so every column type must have `BEq`.
      try mkAppM helper (us.push body)
      catch ex => throwError "{ex.toMessageData}\n\nthis selector returns \
        values, and a returned value is located by `==` — add `deriving BEq` \
        to the returned type"
  let tuples ← evalIdxTuples term
  -- Indexes are minted in walk order, so sorting the index tuples sorts the
  -- rendered selector into walk order; the dedup reads the list as a set.
  let lexLt (a b : List Nat) : Bool := Id.run do
    for (x, y) in a.zip b do
      if x < y then return true
      if x > y then return false
    return a.length < b.length
  let mut out : Array (Array String) := #[]
  let mut prev? : Option (List Nat) := none
  for t in tuples.toArray.qsort lexLt do
    if prev? == some t then continue
    prev? := some t
    let ids := (t.toArray.zip cols).filterMap fun (i, (colIds, _)) => colIds[i]?
    if ids.size == t.length then
      out := out.push ids
  -- The cap counts the *set*: `Tuples` ignores duplicates, so a selector that
  -- returns one tuple many times is small, however long its list.
  if out.size > maxSelectedTuples then
    throwError "raw Lean selector selects {out.size} tuples, over the \
      limit of {maxSelectedTuples}; a diagram op over that many tuples would \
      not render legibly"
  return out

/-! ## Predicates over the represented datum -/

private meta structure PredicateEvidence where
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
meta def evalLeanRel (ctx : LeanSelCtx) (fn : Expr) : MetaM (Array (Array String)) :=
    withoutModifyingState <| withNewMCtxDepth do
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
  let evidence ← preparePredicateEvidence ctx.evidence
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

/-- Tuples as a selector: `` `a1->`a2 + `a3->`a4 ``, or `none` when empty. The
    products bind tighter than the union, so neither side needs parentheses. -/
private meta def tupleUnion (tuples : Array (Array String)) : Sel :=
  tuples.foldl (init := .none_) fun acc ids =>
    let tuple := ids.foldl (init := none) fun t id =>
      some <| match t with | none => .atomLit id | some t => .prod t (.atomLit id)
    match tuple, acc with
    | none, _ => acc
    | some t, .none_ => t
    | some t, a => .union a t

/-! ## Resolution

A congruence over the four selector layers, replacing every embedded Lean leaf with
the tuples it selects and leaving everything else alone. It mirrors
`Sel.freeVars`, which walks the same shape. -/

mutual

meta partial def Sel.resolveLean (ctx : LeanSelCtx) : Sel → MetaM Sel
  | .leanRel fn => return tupleUnion (← evalLeanRel ctx fn)
  | .union a b => return .union (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .diff a b => return .diff (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .inter a b => return .inter (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .prod a b => return .prod (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .prodMult a lm rm b => return .prodMult (← a.resolveLean ctx) lm rm (← b.resolveLean ctx)
  | .join a b => return .join (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .override a b => return .override (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .restrictDom a b => return .restrictDom (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .restrictRan a b => return .restrictRan (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .trans a => return .trans (← a.resolveLean ctx)
  | .reflTrans a => return .reflTrans (← a.resolveLean ctx)
  | .transpose a => return .transpose (← a.resolveLean ctx)
  | .compr binders body => do
    let binders ← binders.mapM fun (x, dom) => return (x, ← dom.resolveLean ctx)
    return .compr binders (← body.resolveLean ctx)
  | e@(.sig ..) | e@(.rel ..) | e@(.var ..) | e@.univ | e@.iden | e@.none_
  | e@(.atomLit ..) | e@(.raw ..) => return e

meta partial def SelInt.resolveLean (ctx : LeanSelCtx) : SelInt → MetaM SelInt
  | .card e => return .card (← e.resolveLean ctx)
  | .proj e => return .proj (← e.resolveLean ctx)
  | .agg op e => return .agg op (← e.resolveLean ctx)
  | .builtin op args => return .builtin op (← args.mapM (·.resolveLean ctx))
  | .sumQuant x dom body =>
    return .sumQuant x (← dom.resolveLean ctx) (← body.resolveLean ctx)
  | e@(.lit ..) => return e

meta partial def SelVal.resolveLean (ctx : LeanSelCtx) : SelVal → MetaM SelVal
  | .label proj e => return .label proj (← e.resolveLean ctx)
  | e@(.ctorLit ..) | e@(.strLit ..) | e@(.boolLit ..) => return e

meta partial def SelForm.resolveLean (ctx : LeanSelCtx) : SelForm → MetaM SelForm
  | .subset a b => return .subset (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .notSubset a b => return .notSubset (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .ni a b => return .ni (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .notNi a b => return .notNi (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .eq a b => return .eq (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .neq a b => return .neq (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .veq a b => return .veq (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .vneq a b => return .vneq (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .icmp op a b => return .icmp op (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .and a b => return .and (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .or a b => return .or (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .xor a b => return .xor (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .iff a b => return .iff (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .implies a b => return .implies (← a.resolveLean ctx) (← b.resolveLean ctx)
  | .ite c t e =>
    return .ite (← c.resolveLean ctx) (← t.resolveLean ctx) (← e.resolveLean ctx)
  | .not a => return .not (← a.resolveLean ctx)
  | .some_ a => return .some_ (← a.resolveLean ctx)
  | .no a => return .no (← a.resolveLean ctx)
  | .lone a => return .lone (← a.resolveLean ctx)
  | .one a => return .one (← a.resolveLean ctx)
  | .quant q disj binders body => do
    let binders ← binders.mapM fun (x, dom) => return (x, ← dom.resolveLean ctx)
    return .quant q disj binders (← body.resolveLean ctx)

end

/-! ## Detecting embedded Lean selectors

Resolution needs the walked datum, and walking it is not free — it also asks
each type for a `SpytialIdentity`, which reports when it cannot derive one. A
spec with no embedded Lean selector needs none of that, so callers check first. -/

mutual

meta partial def Sel.hasLeanRel : Sel → Bool
  | .leanRel _ => true
  | .union a b | .diff a b | .inter a b | .prod a b | .join a b
  | .override a b | .restrictDom a b | .restrictRan a b => a.hasLeanRel || b.hasLeanRel
  | .prodMult a _ _ b => a.hasLeanRel || b.hasLeanRel
  | .trans a | .reflTrans a | .transpose a => a.hasLeanRel
  | .compr binders body =>
    binders.any (fun (_, d) => d.hasLeanRel) || body.hasLeanRel
  | .sig .. | .rel .. | .var .. | .univ | .iden | .none_ | .atomLit .. | .raw .. => false

meta partial def SelInt.hasLeanRel : SelInt → Bool
  | .card e | .proj e | .agg _ e => e.hasLeanRel
  | .builtin _ args => args.any SelInt.hasLeanRel
  | .sumQuant _ dom body => dom.hasLeanRel || body.hasLeanRel
  | .lit .. => false

meta partial def SelVal.hasLeanRel : SelVal → Bool
  | .label _ e => e.hasLeanRel
  | .ctorLit .. | .strLit .. | .boolLit .. => false

meta partial def SelForm.hasLeanRel : SelForm → Bool
  | .subset a b | .notSubset a b | .ni a b | .notNi a b | .eq a b | .neq a b =>
    a.hasLeanRel || b.hasLeanRel
  | .veq a b | .vneq a b => a.hasLeanRel || b.hasLeanRel
  | .icmp _ a b => a.hasLeanRel || b.hasLeanRel
  | .and a b | .or a b | .xor a b | .iff a b | .implies a b =>
    a.hasLeanRel || b.hasLeanRel
  | .ite c t e => c.hasLeanRel || t.hasLeanRel || e.hasLeanRel
  | .not a => a.hasLeanRel
  | .some_ a | .no a | .lone a | .one a => a.hasLeanRel
  | .quant _ _ binders body =>
    binders.any (fun (_, d) => d.hasLeanRel) || body.hasLeanRel

end

/-- Whether any op in `spec` carries an embedded Lean selector. -/
meta def SpytialSpec.hasLeanRel (spec : SpytialSpec) : Bool :=
  spec.any fun stamped => match stamped.op with
    | .orientation s _ | .align s _ | .cyclic s _ | .group s _ _ | .hideAtom s
    | .size s _ _ | .atomStyle s _ _ _ _ | .tag s _ _ | .inferredEdge _ s _ =>
      s.hasLeanRel
    | .edgeStyle .. | .hideField .. | .attribute .. | .flag .. => false

/-- One op's selectors, resolved against the datum. -/
private meta def resolveOp (ctx : LeanSelCtx) : SpytialOp → MetaM SpytialOp
  | .orientation s ds => return .orientation (← s.resolveLean ctx) ds
  | .align s d => return .align (← s.resolveLean ctx) d
  | .cyclic s d => return .cyclic (← s.resolveLean ctx) d
  | .group s n e => return .group (← s.resolveLean ctx) n e
  | .hideAtom s => return .hideAtom (← s.resolveLean ctx)
  | .size s w h => return .size (← s.resolveLean ctx) w h
  | .atomStyle s b f i l => return .atomStyle (← s.resolveLean ctx) b f i l
  | .tag s n v => return .tag (← s.resolveLean ctx) n v
  | .inferredEdge n s l => return .inferredEdge n (← s.resolveLean ctx) l
  | op@(.edgeStyle ..) | op@(.hideField ..) | op@(.attribute ..) | op@(.flag ..) =>
    return op

/-- Rewrite every embedded Lean selector in `spec` into the tuples it selects on
    this datum. Runs before any lowering to SGQ; identity on specs with none.
    The stamp is the user's own text, so resolution leaves it alone: a conflict
    report cites what they wrote, not the atom ids it resolved to. -/
meta def resolveLeanSelectors (datum : Expr) (di : JsonDataInstance)
    (prov : Provenance) (spec : SpytialSpec)
    (evidence : SelectorEvidence := {}) : MetaM SpytialSpec := do
  let ctx : LeanSelCtx := { datum, di, prov, evidence }
  spec.mapM fun stamped => return { stamped with op := ← resolveOp ctx stamped.op }

end

end SpytialLean

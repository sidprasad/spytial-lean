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

/-! # Resolving raw Lean selectors

Each selector becomes one term over arrays of the walked values, run through
Lean's compiled evaluator. The term reports index tuples, and an index into a
column array *is* an atom. -/

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
      -- leave it unapplied.
      let inst ← try synthInstance (← mkAppM ``Decidable #[prop])
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

/-- The walker's sig is a short name, so the definitional check is what keeps a
    same-named type's atoms out of the array, which would otherwise make the
    evaluated term ill-typed. -/
meta def LeanSelCtx.columnFor (ctx : LeanSelCtx) (σ : Expr) :
    MetaM (Array String × Array Expr) := do
  let sig ← sigOfType σ
  let mut ids := #[]
  let mut es := #[]
  for a in ctx.di.atoms do
    if a.type == sig then
      if let some e := ctx.prov[a.id]? then
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
meta def evalLeanRel (ctx : LeanSelCtx) (fn : Expr) : MetaM (Array (Array String)) := do
  let kind ← classifyLeanRel fn
  let cols ← kind.domains.mapM ctx.columnFor
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
      try mkAppM helper (us.push body)
      catch ex => throwError "{ex.toMessageData}\n\nthis selector returns \
        values, and a returned value is located by `==` — add `deriving BEq` \
        to the returned type"
  let tuples ← evalIdxTuples term
  -- Indexes are minted in walk order, so sorting them sorts the rendered
  -- selector into walk order; the dedup reads the list as a set.
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
  if out.size > maxSelectedTuples then
    throwError "raw Lean selector selects {out.size} tuples, over the \
      limit of {maxSelectedTuples}; a diagram op over that many tuples would \
      not render legibly"
  return out

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

/-- Mirrors `Sel.freeVars`, which walks the same shape. -/
meta partial def Sel.resolveLean (ctx : LeanSelCtx) : Sel → MetaM Sel
  | .leanRel fn => return tupleUnion (← evalLeanRel ctx fn)
  | .node c op args => return .node c op (← args.mapM fun
      | .expr e => return .expr (← e.resolveLean ctx)
      | .exprs es => return .exprs (← es.mapM (·.resolveLean ctx))
      | .binders bs =>
        return .binders (← bs.mapM fun (x, d) => return (x, ← d.resolveLean ctx))
      | a@(.name _) | a@(.atom _) => return a)
  | e@(.sig ..) | e@(.rel ..) | e@(.builtin ..) | e@(.var ..) | e@(.num ..)
  | e@(.str ..) | e@(.ctorLit ..) | e@(.boolLit ..) => return e

private meta partial def FieldVal.resolveLean (ctx : LeanSelCtx) :
    FieldVal → MetaM FieldVal
  | .sel s => return .sel (← s.resolveLean ctx)
  | .block fs => return .block (← fs.mapM fun (f, v) => return (f, ← v.resolveLean ctx))
  | v@(.rel ..) | v@(.str ..) | v@(.«enum» ..) | v@(.enums ..) | v@(.num ..)
  | v@(.bool ..) => return v

/-! Callers check these before walking the datum: the walk also asks each type
for a `SpytialIdentity`, which reports when it cannot derive one, and a spec
with no raw Lean selector should not pay for that. -/

meta partial def Sel.hasLeanRel : Sel → Bool
  | .leanRel _ => true
  | .node _ _ args => args.any fun
    | .expr e => e.hasLeanRel
    | .exprs es => es.any Sel.hasLeanRel
    | .binders bs => bs.any fun (_, d) => d.hasLeanRel
    | .name _ | .atom _ => false
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
    (prov : Provenance) (spec : SpytialSpec) : MetaM SpytialSpec := do
  let ctx : LeanSelCtx := { datum, di, prov }
  spec.mapM fun op => return { op with
    fields := ← op.fields.mapM fun (f, v) => return (f, ← v.resolveLean ctx) }

end

end SpytialLean

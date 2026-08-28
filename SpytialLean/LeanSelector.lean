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

`SpytialLean.Sel` states the contract: a Lean selector is a function called on
the value being drawn, returning the selected tuples of values, read as a set.
This file resolves one against a concrete datum.

Resolution builds **one term** per selector and runs it through Lean's own
compiled evaluator — the same machinery as `#eval`. The walked values of each
column are quoted into an array in atom order; the term computes index tuples
into those arrays; an index *is* an atom. Nothing here reduces user code with
`whnf`; the user's function runs as compiled code.

Which term is built depends on the selector's type (`classifyLeanRel`):

* a predicate (`σ₁ → ⋯ → σₙ → Bool`/`Prop`) filters the index product
  directly — no equality instances needed, because nothing is returned;
* a `Spytial.Sel T α` is applied to the datum, and every returned column is
  located by `==` (`BEq`).

Failures are loud. A function from a module that is not `meta import`ed and a
missing `BEq` or `Decidable` instance are reported as errors — never as an
empty selection.

Two boundaries carry over from the walk itself: atoms with no value behind
them (holes, hypotheses, custom-relationalizer emissions) are never selected,
and a column holds one representative value per atom (under structural
identity, *the* value it stands for). -/

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
      let inst ← try synthInstance (← mkAppM ``Decidable #[prop])
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

/-- One column: the walked atoms of type `σ`, with the value behind each, in
    atom order. The evaluated term reports indexes into this array, so an
    index *is* an atom. The walker's sig is a short name; the definitional
    type check keeps a same-named type's atoms out of the array, which would
    otherwise make the evaluated term ill-typed. -/
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

A congruence over the four selector layers, replacing every `leanRel` leaf with
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

/-! ## Detecting raw Lean selectors

Resolution needs the walked datum, and walking it is not free — it also asks
each type for a `SpytialIdentity`, which reports when it cannot derive one. A
spec with no raw Lean selector needs none of that, so callers check first. -/

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

/-- Whether any op in `spec` carries a raw Lean selector. -/
meta def SpytialSpec.hasLeanRel (spec : SpytialSpec) : Bool :=
  spec.any fun
    | .orientation s _ | .align s _ | .cyclic s _ | .group s _ _ | .hideAtom s
    | .size s _ _ | .atomStyle s _ _ _ _ | .tag s _ _ | .inferredEdge _ s _ =>
      s.hasLeanRel
    | .edgeStyle .. | .hideField .. | .attribute .. | .flag .. => false

/-- Rewrite every raw Lean selector in `spec` into the tuples it selects on
    this datum. Runs before any lowering to SGQ; identity on specs with none. -/
meta def resolveLeanSelectors (datum : Expr) (di : JsonDataInstance)
    (prov : Provenance) (spec : SpytialSpec) : MetaM SpytialSpec := do
  let ctx : LeanSelCtx := { datum, di, prov }
  spec.mapM fun
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

end

end SpytialLean

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
* a function (`… → τ`, `… → List/Array/Option τ`) computes its last column,
  and each returned value is located by `==` (`BEq τ`);
* a canonical `Spytial.Sel T α` is applied to the datum, and every returned
  column is located by `==`.

Failures are loud. A function from a module that is not `meta import`ed and a
missing `BEq` or `Decidable` instance are reported as errors — never as an
empty selection.

Two boundaries carry over from the walk itself: atoms with no value behind
them (holes, hypotheses, custom-relationalizer emissions) are never selected,
and with identity merging a column holds one representative value per merged
atom. -/

public section

/-! ## Classifying the selector term -/

/-- The largest tuple a selector may select. -/
meta def maxSelArity : Nat := 4

/-- How the selector term produces its tuples. -/
meta inductive LeanRelShape where
  /-- `… → Bool` / `… → Prop`; every column is enumerated. -/
  | pred (isProp : Bool)
  /-- `… → τ`; the last column is the returned value. -/
  | one
  /-- `… → List τ` / `Array τ` / `Option τ`; one tuple per element. -/
  | many (container : Name)
  /-- The canonical form: the term's type is `Spytial.Sel T α`. -/
  | sel (T : Expr)
  deriving Inhabited

/-- The selector term read as a relation: which types its columns range over,
    and how its tuples are produced. -/
meta structure LeanRelKind where
  /-- For `.sel`, the columns of `α`; otherwise the argument types. -/
  domains : Array Expr
  shape : LeanRelShape
  /-- The computed column's element type; meaningless for `.pred` and `.sel`. -/
  result : Expr
  deriving Inhabited

meta def LeanRelKind.arity (k : LeanRelKind) : Nat :=
  match k.shape with
  | .pred _ | .sel _ => k.domains.size
  | _ => k.domains.size + 1

/-- Every column type, enumerated ones first. -/
meta def LeanRelKind.columns (k : LeanRelKind) : Array Expr :=
  match k.shape with
  | .pred _ | .sel _ => k.domains
  | _ => k.domains.push k.result

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
      return { domains := cols, shape := .sel T, result := α }
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
    return { domains, shape := .pred true, result := ty }
  | _ =>
    if ty.isConstOf ``Bool then
      checkArity domains.size
      return { domains, shape := .pred false, result := ty }
    let mkComputed (shape : LeanRelShape) (τ : Expr) : MetaM LeanRelKind := do
      checkArity (domains.size + 1)
      if domains.size > 2 then
        throwError "a function-valued selector allows at most 2 arguments; \
          write a `Spytial.Sel` for wider relations"
      return { domains, shape, result := τ }
    match ty.getAppFn.constName?, ty.getAppArgs with
    | some c@``List, #[τ] | some c@``Array, #[τ] | some c@``Option, #[τ] =>
      mkComputed (.many c) τ
    | _, _ => mkComputed .one ty

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

/-- What a raw Lean selector resolves against: the datum, the walked instance,
    and the subterm behind each atom. -/
meta structure LeanSelCtx where
  datum : Expr
  di : JsonDataInstance
  prov : Provenance
  /-- Atom → its position in the walk, so results sort in mint order rather
      than in the datum's hash order. -/
  rank : Std.HashMap String Nat

meta def LeanSelCtx.mk' (datum : Expr) (di : JsonDataInstance) (prov : Provenance) :
    LeanSelCtx := Id.run do
  let mut rank : Std.HashMap String Nat := {}
  for i in [:di.atoms.size] do
    rank := rank.insert di.atoms[i]!.id i
  return { datum, di, prov, rank }

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

/-! ## Evaluating one selector -/

/-- The tuples the selector term selects on this datum, as arrays of atom ids. -/
meta def evalLeanRel (ctx : LeanSelCtx) (fn : Expr) : MetaM (Array (Array String)) := do
  let kind ← classifyLeanRel fn
  let cols ← kind.columns.mapM ctx.columnFor
  let us ← (cols.zip kind.columns).mapM fun ((_, es), σ) => mkArrayLit σ es.toList
  -- The half of the contract that needs an instance: a returned value is
  -- located by `==`, so its type must have `BEq`.
  let mkLocated (helper : Name) (args : Array Expr) : MetaM Expr := do
    try mkAppM helper args
    catch ex => throwError "{ex.toMessageData}\n\nthis selector returns \
      values, and a returned value is located by `==` — add `deriving BEq` \
      to the returned type"
  let term ← match kind.shape with
    | .pred isProp =>
      let p ← if isProp then boolifyPred fn kind.domains else pure fn
      let helper := match kind.domains.size with
        | 1 => ``Spytial.Sel.selIdx1
        | 2 => ``Spytial.Sel.selIdx2
        | 3 => ``Spytial.Sel.selIdx3
        | _ => ``Spytial.Sel.selIdx4
      mkAppM helper (us.push p)
    | .one =>
      let helper := if kind.domains.size == 1 then ``Spytial.Sel.selFn1
        else ``Spytial.Sel.selFn2
      mkLocated helper (us.push fn)
    | .many container =>
      let f ← match container with
        | ``Array => mkAppM ``Spytial.Sel.listOfArray #[fn]
        | ``Option => mkAppM ``Spytial.Sel.listOfOption #[fn]
        | _ => pure fn
      let helper := if kind.domains.size == 1 then ``Spytial.Sel.selMany1
        else ``Spytial.Sel.selMany2
      mkLocated helper (us.push f)
    | .sel T =>
      let datumTy ← inferType ctx.datum
      unless ← withNewMCtxDepth (isDefEq datumTy T) do
        throwError "this selector expects a value of type {T}, but the value \
          being drawn has type {datumTy}"
      let body ← mkAppM ``Spytial.Sel.select #[fn, ctx.datum]
      let helper := match kind.domains.size with
        | 1 => ``Spytial.Sel.locate1
        | 2 => ``Spytial.Sel.locate2
        | 3 => ``Spytial.Sel.locate3
        | _ => ``Spytial.Sel.locate4
      mkLocated helper (us.push body)
  let tuples ← evalIdxTuples term
  let mut out : Array (Array String) := #[]
  let mut seen : Std.HashSet String := ∅
  for t in tuples do
    let ids := (t.toArray.zip cols).filterMap fun (i, (ids, _)) => ids[i]?
    if ids.size == t.length then
      let key := "\x00".intercalate ids.toList
      unless seen.contains key do
        seen := seen.insert key
        out := out.push ids
  -- The cap counts the *set*: `Tuples` ignores duplicates, so a selector that
  -- returns one tuple many times is small, however long its list.
  if out.size > maxSelectedTuples then
    throwError "raw Lean selector selects {out.size} tuples, over the \
      limit of {maxSelectedTuples}; a diagram op over that many tuples would \
      not render legibly"
  -- Sort into walk order to keep the rendered selector stable.
  return out.qsort fun a b =>
    Id.run do
      for i in [:min a.size b.size] do
        let ra := ctx.rank[a[i]!]?.getD 0
        let rb := ctx.rank[b[i]!]?.getD 0
        if ra != rb then return ra < rb
      return a.size < b.size

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

/-- Rewrite every raw Lean selector in `spec` into the tuples it selects on
    this datum. Runs before any lowering to SGQ; identity on specs with none. -/
meta def resolveLeanSelectors (datum : Expr) (di : JsonDataInstance)
    (prov : Provenance) (spec : SpytialSpec) : MetaM SpytialSpec := do
  let ctx := LeanSelCtx.mk' datum di prov
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

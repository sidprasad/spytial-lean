module

public import Lean
public meta import SpytialLean.Types
public meta import SpytialLean.Selector
public meta import SpytialLean.Spec
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Meta

/-! # Raw Lean selectors

`hideAtom lean (fun n : RBNode => n matches .nil)` selects by running an
ordinary Lean function over the values the relationalizer walked — no relational
vocabulary, no SGQ, no label round-trip.

The mechanism is the walk's `Provenance` table: every ordinary atom remembers
the (post-whnf) subterm it was minted from. Given a datum, `Sel.leanRel fn`
applies `fn` across the atoms of its domain types, and rewrites itself into the
tuples it selected — `` `a1->`a2->`a3 + `a4->`a5->`a6 ``, the extensional form
spytial-core already resolves by atom id. `resolveLeanSelectors` performs that
rewrite over a whole spec, and every path that renders a spec runs it first.

## Shapes

The type of `fn` fixes the arity, and whether the last column is *enumerated*
or *computed*:

| `fn` | arity | last column |
|------|-------|-------------|
| `σ₁ → ⋯ → σₙ → Bool` (or `Prop`) | n | enumerated: every point of the product is tested |
| `σ₁ → ⋯ → σₖ → τ` | k+1 | computed: every atom holding the returned value |
| `σ₁ → ⋯ → σₖ → List τ` (or `Array`, `Option`) | k+1 | computed: every atom holding each element |

The distinction is cost, not meaning. A predicate on `(p c : Tree)` costs one
decision per *pair* of tree atoms; `fun p : Tree => p.left` costs one call per
atom and selects the same tuples. Predicates are the general form, functions the
one to reach for on anything large — the product is capped, with an error naming
the alternative.

## Boundaries

* A Lean selector selects **by value**. The walk mints an atom per occurrence,
  so a tree with three `.nil` leaves has three atoms holding one value — and a
  selector that picks that value picks all three atoms. Equal values cannot be
  told apart; when the *position* matters, that is what the relational language
  (`left`, `right`, field names) is for.
* Atoms with no subterm to apply a function to — holes, hypotheses, and
  custom-relationalizer emissions — carry no provenance and are never selected.
* With identity merging one atom stands for a class of subterms, and `fn` runs
  on the representative. A computed column resolves by structural equality
  against those representatives, so a returned value that is identity-equal to
  one without being structurally equal to it finds no atom, and drops its tuple.
* A function that gets stuck (an open subterm, no `Decidable` instance) selects
  nothing. `decideProp?` returns `none` rather than guessing.
-/

public section

/-! ## Classifying the function -/

/-- How `fn`'s codomain produces the last column. -/
meta inductive LeanRelShape where
  /-- `… → Bool` / `… → Prop`; every column is enumerated. -/
  | pred (isProp : Bool)
  /-- `… → τ`; the last column is the returned value. -/
  | one
  /-- `… → List τ` / `Array τ` / `Option τ`; one tuple per element. -/
  | many (container : Name)
  deriving Repr, BEq, Inhabited

/-- `fn` read as a relation: which types its columns range over, and how the
    last one is produced. -/
meta structure LeanRelKind where
  /-- The enumerated columns, in order — `fn`'s argument types. -/
  domains : Array Expr
  shape : LeanRelShape
  /-- The computed column's element type; meaningless for `.pred`. -/
  result : Expr
  deriving Inhabited

meta def LeanRelKind.arity (k : LeanRelKind) : Nat :=
  k.domains.size + (if k.shape matches .pred _ then 0 else 1)

/-- Every column type, enumerated ones first. -/
meta def LeanRelKind.columns (k : LeanRelKind) : Array Expr :=
  if k.shape matches .pred _ then k.domains else k.domains.push k.result

/-- Read `fn`'s type as a relation. Shared by the elaborator (which needs the
    arity to check the op position) and by resolution, so the two cannot drift.
    Throws the user-facing rejection. -/
meta def classifyLeanRel (fn : Expr) : MetaM LeanRelKind := do
  let mut domains := #[]
  let mut ty ← whnf (← inferType fn)
  -- Peel non-dependent arrows; a dependent one ends the argument list.
  while ty matches .forallE .. do
    let .forallE _ dom body _ := ty | unreachable!
    if body.hasLooseBVars then break
    domains := domains.push dom
    ty ← whnf body
  if domains.isEmpty then
    throwError "a raw Lean selector must be a function over the walked types, \
      but this term has type {← inferType fn}"
  if ty matches .forallE .. then
    throwError "a raw Lean selector cannot have a dependent argument type; \
      this one has type {← inferType fn}"
  match ty with
  | .sort .zero => return { domains, shape := .pred true, result := ty }
  | _ =>
    if ty.isConstOf ``Bool then
      return { domains, shape := .pred false, result := ty }
    match ty.getAppFn.constName?, ty.getAppArgs with
    | some c@``List, #[τ] | some c@``Array, #[τ] | some c@``Option, #[τ] =>
      return { domains, shape := .many c, result := τ }
    | _, _ => return { domains, shape := .one, result := ty }

/-! ## Evaluation -/

/-- Ceiling on the enumerated product. One decision per point is the same budget
    the walker spends on identity, but a runaway deserves an error. -/
private meta def maxSelectorEvals : Nat := 4096

/-- What a raw Lean selector resolves against: the walked datum, the subterm
    behind each atom, and two indexes over them. -/
meta structure LeanSelCtx where
  di : JsonDataInstance
  prov : Provenance
  /-- Subterm → every atom holding it, in atom order. -/
  located : Std.HashMap ExprStructEq (Array String)
  /-- Atom → its position in the walk, so results sort in mint order rather
      than in the datum's hash order. -/
  rank : Std.HashMap String Nat

meta def LeanSelCtx.mk' (di : JsonDataInstance) (prov : Provenance) : LeanSelCtx := Id.run do
  let mut located : Std.HashMap ExprStructEq (Array String) := {}
  for a in di.atoms do
    if let some e := prov[a.id]? then
      located := located.insert ⟨e⟩ ((located[(⟨e⟩ : ExprStructEq)]?.getD #[]).push a.id)
  let mut rank : Std.HashMap String Nat := {}
  for i in [:di.atoms.size] do
    rank := rank.insert di.atoms[i]!.id i
  return { di, prov, located, rank }

/-- Every atom holding this value — empty when the walk minted none for it. A
    value can be held by several atoms (three `.nil` leaves are three atoms,
    one value); a computed column selects all of them, because a value carries
    no occurrence and picking one would be a guess. -/
private meta def LeanSelCtx.atomsOf (ctx : LeanSelCtx) (v : Expr) : MetaM (Array String) := do
  return (ctx.located[(⟨← whnf v⟩ : ExprStructEq)]?).getD #[]

/-- The elements of a closed `List` value. `none` if the spine does not reduce. -/
private meta partial def listElems? (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← whnf e
  match e.getAppFn.constName? with
  | some ``List.nil => return some #[]
  | some ``List.cons =>
    let args := e.getAppArgs
    if h : args.size = 3 then
      let some rest ← listElems? args[2] | return none
      return some (#[args[1]] ++ rest)
    else return none
  | _ => return none

/-- The elements the computed column ranges over, for a `.many` codomain. -/
private meta def containerElems? (container : Name) (e : Expr) :
    MetaM (Option (Array Expr)) := do
  match container with
  | ``List => listElems? e
  | ``Array => listElems? (← mkAppM ``Array.toList #[e])
  | _ =>
    let e ← whnf e
    match e.getAppFn.constName? with
    | some ``Option.none => return some #[]
    | some ``Option.some => return some #[e.appArg!]
    | _ => return none

/-- Every point of `columns`' product, as index tuples. -/
private meta def productPoints (sizes : Array Nat) : Array (Array Nat) :=
  sizes.foldl (init := #[#[]]) fun acc n =>
    acc.flatMap fun pt => (Array.range n).map pt.push

/-- The tuples `fn` selects on this datum, as arrays of atom ids. -/
meta def evalLeanRel (ctx : LeanSelCtx) (fn : Expr) : MetaM (Array (Array String)) := do
  let kind ← classifyLeanRel fn
  -- Enumerated columns: the atoms of each domain sig, with their subterms.
  let mut cols : Array (Array (String × Expr)) := #[]
  for dom in kind.domains do
    let sig ← sigOfType dom
    cols := cols.push <| ctx.di.atoms.filterMap fun a =>
      if a.type == sig then (ctx.prov[a.id]?).map (a.id, ·) else none
  let total := cols.foldl (init := 1) (· * ·.size)
  if total > maxSelectorEvals then
    throwError "raw Lean selector ranges over {total} points \
      ({" × ".intercalate (cols.toList.map (toString ·.size))}), over the limit \
      of {maxSelectorEvals}; a function-valued selector computes its last \
      column instead of enumerating it"
  let mut out : Array (Array String) := #[]
  for pt in productPoints (cols.map (·.size)) do
    let cells := pt.zipWith (fun i col => col[i]!) cols
    let ids := cells.map (·.1)
    let res := mkAppN fn (cells.map (·.2))
    match kind.shape with
    | .pred isProp =>
      let verdict ← if isProp then decideProp? res else evalBool? res
      if verdict == some true then out := out.push ids
    | .one =>
      for id in ← ctx.atomsOf res do
        out := out.push (ids.push id)
    | .many container =>
      let some elems ← containerElems? container res | continue
      for v in elems do
        for id in ← ctx.atomsOf v do
          let tuple := ids.push id
          unless out.contains tuple do out := out.push tuple
  -- The datum lists relations in hash order, so sort into walk order to keep
  -- the rendered selector stable.
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

/-- Rewrite every raw Lean selector in `spec` into the tuples it selects on this
    datum. Runs before any lowering to SGQ; identity on specs with none. -/
meta def resolveLeanSelectors (di : JsonDataInstance) (prov : Provenance)
    (spec : SpytialSpec) : MetaM SpytialSpec := do
  let ctx := LeanSelCtx.mk' di prov
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

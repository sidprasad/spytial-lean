module

public import Lean
public import SpytialLean.Enum

namespace SpytialLean

open Lean Meta

/-! Single source of truth for the relationalizer's naming, so static checkers
predict the same names the runtime walker emits. -/

public meta def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => "_"

public meta def ppLabel (e : Expr) : MetaM String := do
  return toString (← Meta.ppExpr e)

public meta def typeHead? (ty : Expr) : MetaM (Option Name) := do
  match (← Meta.whnf ty).getAppFn with
  | .const n _ => return some n
  | _          => return none

public meta def sigOfType (ty : Expr) : MetaM String := do
  match ← typeHead? ty with
  | some n => return shortName n
  | none   => ppLabel ty

public meta def ctorDataBinderNames (ci : ConstructorVal) : Array Name := Id.run do
  let mut binderNames : Array Name := #[]
  let mut ctorTy := ci.type
  let mut paramIdx := 0
  while ctorTy.isForall do
    if paramIdx ≥ ci.numParams then
      binderNames := binderNames.push ctorTy.bindingName!
    paramIdx := paramIdx + 1
    ctorTy := ctorTy.bindingBody!
  return binderNames

/-- Positional ctor args carry inaccessible hygienic binder names (`a✝`), not
    `.anonymous`, so macro-scoped names take the `ctor_i` fallback. -/
public meta def fieldRelName (ctorShort : String) (binderNames : Array Name) (i : Nat) : String :=
  if h : i < binderNames.size then
    let n := binderNames[i]
    if n.isAnonymous || n.hasMacroScopes then s!"{ctorShort}_{i}" else toString n
  else
    s!"{ctorShort}_{i}"

/-- The label the relationalizer assigns to a hole (an unassigned metavariable):
    `?` when anonymous, `?name` for a user-named hole. Macro-scoped names count as
    anonymous — they are synthetic, not something the user wrote. -/
public meta def holeLabel (userName : Name) : String :=
  if userName.isAnonymous || userName.hasMacroScopes then "?"
  else s!"?{userName}"

/-- The label the relationalizer assigns to a hypothesis (`fvar`) leaf: its user name
    with macro scopes erased (so inaccessible names render without the dagger),
    falling back to `?` for genuinely anonymous binders. -/
public meta def hypLabel (userName : Name) : String :=
  let n := userName.eraseMacroScopes
  if n.isAnonymous then "?" else toString n

/-- Whether the walker erases a value of this type — proofs (`Prop`) and types
    (`Sort`) — and so drops fields of it. -/
public meta def isProofLikeType (ty : Expr) : MetaM Bool := do
  return (← Meta.isProp ty) || ty.isSort

/-! ## Function tabulation

Shared with the static checkers, so a predicted relation cannot drift from an
emitted one. -/

/-- How far the element list is unrolled before a domain is called too big.
    Bounds a wide `Fin`, and anything whose instance builds a large product. -/
private meta def enumFuel : Nat := 512

/-- Elements of a `List α` expression whose spine reduces to literals. -/
private meta partial def listElems? (e : Expr) (fuel : Nat) : MetaM (Option (Array Expr)) := do
  if fuel == 0 then return none
  match (← Meta.whnf e).getAppFnArgs with
  | (``List.nil, _) => return some #[]
  | (``List.cons, #[_, hd, tl]) => do
    let some rest ← listElems? tl (fuel - 1) | return none
    return some (#[hd] ++ rest)
  | _ => return none

/-- A type the class can even be applied to: `SpytialEnum` is `Type u`-only,
    and a proposition is never a drawable domain. Without this the class
    application is a type error rather than a decline. -/
private meta def isEnumCandidate (ty : Expr) : MetaM Bool := do
  let .sort u ← Meta.whnf (← inferType ty) | return false
  return !u.isZero

/-- Derive `SpytialEnum` for whatever in `ty` is missing one.

    The type arguments matter as much as the head: `Par × St` fails to
    synthesize even though `Prod` has an instance, because neither side does.
    Deriving only the head would leave that domain undrawable. -/
private meta partial def deriveEnum (ty : Expr) : MetaM Unit := do
  let ty ← Meta.whnf ty
  for a in ty.getAppArgs do
    if ← isEnumCandidate a then deriveEnum a
  if (← Meta.synthInstance? (← mkAppM ``SpytialEnum #[ty])).isSome then return
  let .const declName _ := ty.getAppFn | return
  try
    Lean.liftCommandElabM <| Lean.Elab.applyDerivingHandlers ``SpytialEnum #[declName]
    resetSynthInstanceCache
  catch _ => pure ()

/-- `SpytialEnum ty`, deriving what it needs on the spot.

    This is what `#eval` does for a missing `Repr` (`eval.derive.repr`), and
    for the same reason: a plain user inductive should draw without anyone
    writing a `deriving` clause. The handler refuses recursive, indexed and
    dependent types, so "no instance" stays a real answer. -/
private meta def synthEnum? (ty : Expr) : MetaM (Option Expr) := do
  unless ← isEnumCandidate ty do return none
  if let some inst ← Meta.synthInstance? (← mkAppM ``SpytialEnum #[ty]) then
    return some inst
  deriveEnum ty
  Meta.synthInstance? (← mkAppM ``SpytialEnum #[ty])

/-- A constructor is worth its own name; anything else is pretty-printed. -/
private meta def elemLabel (e : Expr) : MetaM String := do
  match e.getAppFn with
  | .const n _ =>
    if (← getEnv).find? n matches some (.ctorInfo _) then return shortName n else ppLabel e
  | _ => ppLabel e

/-- Try to enumerate all elements of a finite type.
    Returns `some [(label, expr)]` for finite types, `none` otherwise. -/
public meta def tryEnumerateDomain (ty : Expr) : MetaM (Option (Array (String × Expr))) := do
  let ty ← Meta.whnf ty
  let some inst ← synthEnum? ty | return none
  let lst ← mkAppOptM ``SpytialEnum.elems #[some ty, some inst]
  let some elems ← listElems? lst enumFuel | return none
  elems.mapM fun e => return ((← elemLabel e), e)

public meta inductive CodomainKind where
  | data
  | prop
  deriving BEq, Repr, Inhabited

public meta structure TabulationBinder where
  domain : Expr
  elems : Array (String × Expr)

/-- How a function type tabulates: one column per binder, then the codomain. -/
public meta structure TabulationPlan where
  binders : Array TabulationBinder
  codomain : Expr
  kind : CodomainKind

/-- Points in the domain product — the tuple count of the emitted table. -/
public meta def TabulationPlan.size (p : TabulationPlan) : Nat :=
  p.binders.foldl (fun n b => n * b.elems.size) 1

/-- The columns after the owner: the binders, then a data codomain's result
    (a proposition's extension has none). -/
public meta def TabulationPlan.tailTypes (p : TabulationPlan) : Array Expr :=
  let domains := p.binders.map (·.domain)
  match p.kind with
  | .data => domains.push p.codomain
  | .prop => domains

public meta def TabulationPlan.arity (p : TabulationPlan) : Nat :=
  1 + p.tailTypes.size

/-- Column type heads, standing in for the function type no atom ever gets. -/
public meta def TabulationPlan.columnHeads (p : TabulationPlan) : MetaM (Array Name) :=
  p.tailTypes.filterMapM typeHead?

private meta partial def peelBinders (ty : Expr) (acc : Array TabulationBinder) :
    MetaM (Option TabulationPlan) := do
  match ← Meta.whnf ty with
  | .forallE _ dom body _ =>
    -- a dependent telescope has no rectangular table
    if body.hasLooseBVar 0 then return none
    let some elems ← tryEnumerateDomain dom | return none
    peelBinders body (acc.push { domain := dom, elems })
  | cod =>
    if acc.isEmpty then return none
    -- the codomain of a relation is the sort `Prop`, not a proposition
    let kind := match cod with
      | .sort l => if l.isZero then CodomainKind.prop else .data
      | _ => .data
    return some { binders := acc, codomain := cod, kind }

/-- The table a function type tabulates into, or `none` when it does not. -/
public meta def tabulationPlan? (ty : Expr) : MetaM (Option TabulationPlan) :=
  peelBinders ty #[]

/-- What a tabulating field's type emits, as a static checker needs it. -/
public meta structure FieldTable where
  arity : Nat
  columnHeads : Array Name
  deriving Repr, Inhabited

public meta def FieldTable.of? (ty : Expr) : MetaM (Option FieldTable) := do
  let some plan ← tabulationPlan? ty | return none
  return some { arity := plan.arity, columnHeads := ← plan.columnHeads }

public meta structure FieldShape where
  relName : String
  typeSig : Option String
  /-- Head constant of the field type, when it has one; `none` for a type
      parameter or function type (unpredictable vocabulary). -/
  typeHead : Option Name := none
  /-- The walker drops this field: it is `Prop`- or `Sort`-typed. -/
  isProofLike : Bool
  /-- Set when the field's type tabulates: its columns, not its type head, are
      the vocabulary its values contribute. -/
  table : Option FieldTable := none
  /-- The emitted relation's arity, when the declaration fixes it. A function
      type over the inductive's own parameters fixes nothing: only the
      instantiation decides leaf or table. -/
  arity? : Option Nat := some 2
  deriving Repr, Inhabited

public meta structure CtorShape where
  ctorName : Name
  ctorShort : String
  fields : Array FieldShape
  deriving Repr, Inhabited

public meta structure TypeShape where
  typeName : Name
  sig : String
  ctors : Array CtorShape
  deriving Repr, Inhabited

public meta def TypeShape.ofInductive (typeName : Name) : MetaM (Option TypeShape) := do
  let env ← getEnv
  let some (.inductInfo ii) := env.find? typeName | return none
  let mut ctors : Array CtorShape := #[]
  for ctorName in ii.ctors do
    let some (.ctorInfo ci) := env.find? ctorName | continue
    let ctorShort := shortName ctorName
    let binderNames := ctorDataBinderNames ci
    let fields ← Meta.forallTelescopeReducing ci.type fun xs _ => do
      let dataXs := xs.extract ci.numParams xs.size
      let mut fs : Array FieldShape := #[]
      for i in [:dataXs.size] do
        let xty ← Meta.inferType dataXs[i]!
        let isProofLike ← isProofLikeType xty
        let (typeSig, typeHead) ←
          match (← Meta.whnf xty).getAppFn with
          | .const n _ => pure (some (shortName n), some n)
          | _          => pure (none, none)
        let table ← FieldTable.of? xty
        let arity? ← match table with
          | some t => pure (some t.arity)
          | none => pure (if (← Meta.whnf xty).isForall && xty.hasFVar then none else some 2)
        fs := fs.push { relName := fieldRelName ctorShort binderNames i,
                        typeSig, typeHead, isProofLike, table, arity? }
      return fs
    ctors := ctors.push { ctorName, ctorShort, fields }
  return some { typeName, sig := shortName typeName, ctors }

public meta def TypeShape.dataRelNames (ts : TypeShape) : Array String := Id.run do
  let mut out : Array String := #[]
  for c in ts.ctors do
    for f in c.fields do
      unless f.isProofLike do
        out := out.push f.relName
  return out

end SpytialLean

module

public import Lean

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
    (`Sort`) — and so drops fields of it. The one predicate the walker
    (`isProofArg`) and the static checker share. -/
public meta def isProofLikeType (ty : Expr) : MetaM Bool := do
  return (← Meta.isProp ty) || ty.isSort

/-! ## Function tabulation

Which function types the walker turns into flat n-ary tables, and the columns
those tables get. Shared with the static checkers, so a predicted relation
cannot drift from an emitted one. -/

/-- Try to enumerate all elements of a finite type.
    Returns `some [(label, expr)]` for finite types, `none` otherwise. -/
public meta def tryEnumerateDomain (ty : Expr) : MetaM (Option (Array (String × Expr))) := do
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

/-- Whether a tabulated function yields data or a proposition. -/
public meta inductive CodomainKind where
  | data
  | prop
  deriving BEq, Repr, Inhabited

/-- One tabulated binder: its domain type and that domain's elements. -/
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

/-- The table a function type tabulates into, or `none` when it does not: a
    non-function, a dependent telescope, or a domain that does not enumerate. -/
public meta def tabulationPlan? (ty : Expr) : MetaM (Option TabulationPlan) :=
  peelBinders ty #[]

public meta structure FieldShape where
  relName : String
  typeSig : Option String
  /-- Head constant of the field type, when it has one; `none` for a type
      parameter or function type (unpredictable vocabulary). -/
  typeHead : Option Name := none
  /-- The walker drops this field: it is `Prop`- or `Sort`-typed. -/
  isProofLike : Bool
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
        fs := fs.push { relName := fieldRelName ctorShort binderNames i,
                        typeSig, typeHead, isProofLike }
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

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

/-- Const heads of a type application's *type* arguments, recursively
    (`List (Node GraderKind)` → `#[Node, GraderKind]`), so scope closures can
    see through polymorphic containers even where a field's type is a bare
    parameter of the container. Value arguments (`Fin 3`'s `3`) and anything
    without a constant head contribute no vocabulary and are skipped. -/
public meta partial def typeConstArgHeads (ty : Expr) : MetaM (Array Name) := do
  ty.getAppArgs.flatMapM fun arg => do
    let arg ← Meta.whnf arg
    let inner ← typeConstArgHeads arg
    let .const n _ := arg.getAppFn | return inner
    return if (← Meta.inferType arg).isSort then #[n] ++ inner else inner

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

public meta structure FieldShape where
  relName : String
  typeSig : Option String
  /-- Head constant of the field type, when it has one; `none` for a type
      parameter or function type (unpredictable vocabulary). -/
  typeHead : Option Name := none
  /-- Const heads of the field type's type arguments (`deps : List Node` →
      `#[Node]`); the scope closure follows these so a container's element
      vocabulary is known. -/
  typeArgHeads : Array Name := #[]
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
        let xty ← Meta.whnf xty
        let (typeSig, typeHead) ←
          match xty.getAppFn with
          | .const n _ => pure (some (shortName n), some n)
          | _          => pure (none, none)
        fs := fs.push { relName := fieldRelName ctorShort binderNames i,
                        typeSig, typeHead,
                        typeArgHeads := ← typeConstArgHeads xty, isProofLike }
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

import Lean

namespace SpytialLean

open Lean Meta

/-! Single source of truth for the relationalizer's naming, so static checkers
predict the same names the runtime walker emits. -/

def shortName (n : Name) : String :=
  match n with
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => "_"

def ppLabel (e : Expr) : MetaM String := do
  return toString (← Meta.ppExpr e)

def typeHead? (ty : Expr) : MetaM (Option Name) := do
  match (← Meta.whnf ty).getAppFn with
  | .const n _ => return some n
  | _          => return none

def sigOfType (ty : Expr) : MetaM String := do
  match ← typeHead? ty with
  | some n => return shortName n
  | none   => ppLabel ty

def ctorDataBinderNames (ci : ConstructorVal) : Array Name := Id.run do
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
def fieldRelName (ctorShort : String) (binderNames : Array Name) (i : Nat) : String :=
  if h : i < binderNames.size then
    let n := binderNames[i]
    if n.isAnonymous || n.hasMacroScopes then s!"{ctorShort}_{i}" else toString n
  else
    s!"{ctorShort}_{i}"

structure FieldShape where
  relName : String
  typeSig : Option String
  isProp : Bool
  deriving Repr, Inhabited

structure CtorShape where
  ctorName : Name
  ctorShort : String
  fields : Array FieldShape
  deriving Repr, Inhabited

structure TypeShape where
  typeName : Name
  sig : String
  ctors : Array CtorShape
  deriving Repr, Inhabited

def TypeShape.ofInductive (typeName : Name) : MetaM (Option TypeShape) := do
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
        let isP ← Meta.isProp xty
        let typeSig ←
          match (← Meta.whnf xty).getAppFn with
          | .const n _ => pure (some (shortName n))
          | _          => pure none
        fs := fs.push { relName := fieldRelName ctorShort binderNames i, typeSig, isProp := isP }
      return fs
    ctors := ctors.push { ctorName, ctorShort, fields }
  return some { typeName, sig := shortName typeName, ctors }

def TypeShape.dataRelNames (ts : TypeShape) : Array String := Id.run do
  let mut out : Array String := #[]
  for c in ts.ctors do
    for f in c.fields do
      unless f.isProp do
        out := out.push f.relName
  return out

end SpytialLean

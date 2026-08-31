module

public import Lean
public meta import Lean.Elab.Deriving.Basic

namespace SpytialLean

open Lean Meta Elab Command Term

/-! # Listing a finite type

A function becomes a relation by evaluating it at every point of its domain, so
a domain is drawable exactly when it can be listed. A class rather than a match
on the type head, so the walker asks the type instead of knowing about it and
`enumElems?` can derive a missing instance on demand. -/

/-- Element order is draw order, so it is part of the diagram; a derived
    instance lists in constructor-declaration order. -/
public class SpytialEnum (α : Type u) where
  elems : List α

namespace SpytialEnum

public instance : SpytialEnum Bool := ⟨[false, true]⟩
public instance : SpytialEnum Unit := ⟨[()]⟩
public instance : SpytialEnum (Fin n) := ⟨List.finRange n⟩

public instance [SpytialEnum α] [SpytialEnum β] : SpytialEnum (α × β) :=
  ⟨(elems : List α).flatMap fun a => (elems : List β).map fun b => (a, b)⟩

public instance [SpytialEnum α] : SpytialEnum (Option α) :=
  ⟨none :: (elems : List α).map some⟩

public instance [SpytialEnum α] [SpytialEnum β] : SpytialEnum (α ⊕ β) :=
  ⟨(elems : List α).map Sum.inl ++ (elems : List β).map Sum.inr⟩

end SpytialEnum

/-! ## Deriving

Only a monomorphic, non-indexed inductive derives: a parameter or a universe
variable would need an instance-implicit binder the handler does not emit,
which is why `Prod`, `Sum` and `Option` are written out above. Refusing a field
that mentions the type itself is what stops `Nat` from producing an `elems`
defined in terms of itself. -/

private meta def ctorElemsTerm (declName : Name) (ctorName : Name) : MetaM (Option Term) := do
  let some (.ctorInfo ci) := (← getEnv).find? ctorName | return none
  forallTelescopeReducing ci.type fun fields _ => do
    let fields := fields.extract ci.numParams fields.size
    let mut binders : Array (Ident × Term) := #[]
    for f in fields do
      let ty ← inferType f
      if ty.hasLooseBVars || ty.getUsedConstants.contains declName then return none
      if ← isProp ty then return none
      binders := binders.push (mkIdent (← mkFreshUserName `x), ← PrettyPrinter.delab ty)
    let mut body ← `([$(Syntax.mkApp (mkIdent ctorName) (binders.map (·.1))):term])
    for (x, ty) in binders.reverse do
      body ← `((SpytialEnum.elems (α := $ty)).flatMap fun $x => $body)
    return some body

private meta def mkInstanceCmd (declName : Name) (ii : InductiveVal) :
    TermElabM (Option (TSyntax `command)) := do
  let declId := mkIdent declName
  let mut all ← `(([] : List $declId))
  for ctorName in ii.ctors do
    let some part ← ctorElemsTerm declName ctorName | return none
    all ← `($all ++ $part)
  return some (← `(instance : SpytialEnum $declId := ⟨$all⟩))

public meta def mkSpytialEnumHandler (declNames : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  for declName in declNames do
    let some (.inductInfo ii) := env.find? declName | return false
    unless ii.numIndices == 0 && ii.numParams == 0 && ii.levelParams.isEmpty do return false
    let some cmd ← liftTermElabM (mkInstanceCmd declName ii) | return false
    elabCommand cmd
  return true

meta initialize
  registerDerivingHandler ``SpytialEnum mkSpytialEnumHandler

/-! ## Listing on demand -/

/-- So a wide `Fin` or a large product declines rather than spending the whole
    walk on one domain. -/
private meta def enumFuel : Nat := 512

private meta partial def listElems? (e : Expr) (fuel : Nat) : MetaM (Option (Array Expr)) := do
  if fuel == 0 then return none
  match (← Meta.whnf e).getAppFnArgs with
  | (``List.nil, _) => return some #[]
  | (``List.cons, #[_, hd, tl]) => do
    let some rest ← listElems? tl (fuel - 1) | return none
    return some (#[hd] ++ rest)
  | _ => return none

/-- The class is `Type u`-indexed, so applying it to a proposition would be a
    type error rather than a decline. -/
private meta def isEnumCandidate (ty : Expr) : MetaM Bool := do
  let .sort u ← Meta.whnf (← inferType ty) | return false
  return !u.isZero

/-- The arguments matter as much as the head: `Par × St` fails to synthesize
    even though `Prod` has an instance, because neither side does. A failed
    derivation leaves a `sorryAx`-bodied instance behind, hence the `setEnv`. -/
private meta partial def deriveEnum (ty : Expr) : MetaM Unit := do
  let ty ← Meta.whnf ty
  for a in ty.getAppArgs do
    if ← isEnumCandidate a then deriveEnum a
  if (← Meta.synthInstance? (← mkAppM ``SpytialEnum #[ty])).isSome then return
  let .const declName _ := ty.getAppFn | return
  let env ← getEnv
  try
    Lean.liftCommandElabM <| Lean.Elab.applyDerivingHandlers ``SpytialEnum #[declName]
    resetSynthInstanceCache
  catch _ => setEnv env

private meta def synthEnum? (ty : Expr) : MetaM (Option Expr) := do
  unless ← isEnumCandidate ty do return none
  if let some inst ← Meta.synthInstance? (← mkAppM ``SpytialEnum #[ty]) then
    return some inst
  deriveEnum ty
  Meta.synthInstance? (← mkAppM ``SpytialEnum #[ty])

/-- Derives on demand, so it mutates the environment, which the signature does
    not suggest. For wide types `whnf` hits `maxRecDepth` before `enumFuel`
    counts an element, and `Core.tryCatch` rethrows that exception, so declining
    takes `tryCatchRuntimeEx`. -/
public meta def enumElems? (ty : Expr) : MetaM (Option (Array Expr)) := do
  let ty ← Meta.whnf ty
  let some inst ← synthEnum? ty | return none
  let elems ← mkAppOptM ``SpytialEnum.elems #[some ty, some inst]
  tryCatchRuntimeEx (listElems? elems enumFuel) fun e =>
    if e.isMaxRecDepth then return none else throw e

end SpytialLean

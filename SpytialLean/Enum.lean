module

public import Lean
public meta import Lean.Elab.Deriving.Basic

namespace SpytialLean

open Lean Meta Elab Command Term

/-! # Listing a finite type

The relationalizer turns a function into a relation by evaluating it at every
point of its domain, so a domain is drawable exactly when it can be listed.
This module is that judgement, as a class rather than as a match on the type
head: the walker asks the type instead of knowing about it.

Primitives ship instances here. Everything else is derived, and derived *on
demand* — `tryEnumerateDomain` runs this handler itself when synthesis comes up
empty, the way `#eval` derives a missing `Repr`. So a user type needs no
`deriving` clause to be drawable, which is what the hard-coded all-nullary case
used to buy. -/

/-- Every element of a finite type, each exactly once.

    The order is the order they are drawn in, so it is part of the diagram:
    constructor-declaration order for a derived instance. -/
public class SpytialEnum (α : Type u) where
  /-- Every element, once. -/
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

Refused, rather than derived wrong: an indexed family, a dependent field (its
type is not fixed until the earlier fields are chosen), and any constructor
field mentioning the type itself — that last one is what stops `Nat` and `List`
from producing an instance whose `elems` is defined in terms of itself. -/

private meta def ctorElemsTerm (declName : Name) (ctorName : Name) : MetaM (Option Term) := do
  let some (.ctorInfo ci) := (← getEnv).find? ctorName | return none
  forallTelescopeReducing ci.type fun fields _ => do
    let fields := fields.extract ci.numParams fields.size
    let ctorId := mkIdent ctorName
    let mut binders : Array (Ident × Term) := #[]
    for f in fields do
      let ty ← inferType f
      if ty.hasLooseBVars || (ty.getUsedConstants.contains declName) then return none
      if (← isProp ty) then return none
      binders := binders.push (mkIdent (← mkFreshUserName `x), ← PrettyPrinter.delab ty)
    let args := binders.map (·.1)
    let mut body ← `([$(mkAppN' ctorId args):term])
    for (x, ty) in binders.reverse do
      body ← `((SpytialEnum.elems (α := $ty)).flatMap fun $x => $body)
    return some body
where
  mkAppN' (f : Ident) (args : Array Ident) : Term :=
    args.foldl (fun acc a => Syntax.mkApp acc #[a]) (f : Term)

/-- The instance command for one inductive, or `none` when a constructor
    refuses. -/
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

end SpytialLean

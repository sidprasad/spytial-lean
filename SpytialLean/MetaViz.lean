module

public import Lean
public import SpytialLean.Identity
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.Command

namespace SpytialLean

open Lean Meta

/-! # Lean's own metaprogramming values under the walker

A `Name` walks as its cons spine: five atoms for `` `HAdd.hAdd `` that say
nothing its literal would not. `Expr` can neither derive an identity (its
`KVMap` reaches `Syntax`) nor want one: a syntax view keeps two occurrences
of `bvar 0` apart. Both policies live here; `ExprView.lean` draws `Expr`. -/

/-- The name a closed `Name` chain spells, read off the constructors. `none`
    for a stuck or open chain. -/
private meta partial def nameOf? (e : Expr) : MetaM (Option Name) := do
  let e ← whnf e
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Lean.Name.anonymous, #[] => return some .anonymous
  | some ``Lean.Name.str, #[p, s] => do
    let some pre ← nameOf? p | return none
    let .lit (.strVal str) ← whnf s | return none
    return some (.str pre str)
  | some ``Lean.Name.num, #[p, i] => do
    let some pre ← nameOf? p | return none
    let .lit (.natVal n) ← whnf i | return none
    return some (.num pre n)
  | _, _ => return none

/-- One leaf per `Name`, labeled with its literal; a stuck or open chain is
    labeled by the pretty-printer. -/
public meta def nameLeaf : CustomRelationalizer := fun e _ => do
  let label ← do
    match ← nameOf? e with
    | some n => pure (if n.isAnonymous then "anonymous" else s!"`{n}")
    | none => ppLabel (← whnf e)
  emitAtom "Name" label

spytial_relationalizer Lean.Name nameLeaf

/-- Position is the meaning in a syntax view; nothing derivable exists either. -/
public instance : SpytialIdentity Lean.Expr := .asWritten

end SpytialLean

module

public import Lean
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Meta

public section

/-! # Bounded model finding

The Lean-side half of proof-state diagramming: given `x : T` and the
hypotheses that mention it, *find* concrete values of `x` consistent with
them, so the diagram can show what the hole CAN be — not only what is known
about it.

The search is scope-bounded, Alloy-style: `enumerateValues` generates every
value of an inductive type up to a constructor depth, and each candidate is
checked against the hypotheses by substitution + `decideProp?` (`Decidable`
instances). A hypothesis with no decision procedure — or one left open by
other variables — filters nothing and is reported as *unchecked*, never
silently assumed. Zero surviving candidates is itself information: within
the bound, the hole cannot look like anything.

Spytial stays the renderer: a found model is injected as a refinement
(`WalkConfig.refinements`), so the state draws with `x` instantiated and
every constraint edge (`≠`, relations, the goal) pointing into the model's
structure. -/

/-- Every value of `ty` built from at most `depth` nested constructors, up
    to `cap` values. Finite bases (`Bool`, `Fin n`, nullary-constructor
    enums) come from `tryEnumerateDomain`; `Nat` is cut to the literals
    `0 … depth`; other non-indexed inductives enumerate constructor-wise,
    fields at `depth - 1`. An unenumerable type (a variable, a function, an
    indexed family, a proof-carrying constructor) contributes nothing. -/
public meta partial def enumerateValues (ty : Expr) (depth : Nat) (cap : Nat := 512) :
    MetaM (Array Expr) := do
  if let some elems ← tryEnumerateDomain ty then
    return elems.map (·.2)
  let ty ← whnf ty
  match ty.getAppFn with
  | .const ``Nat _ =>
    return (Array.range (min (depth + 1) cap)).map (mkRawNatLit ·)
  | .const indName lvls => do
    let env ← getEnv
    let some (.inductInfo ii) := env.find? indName | return #[]
    unless ii.numIndices == 0 do return #[]
    if depth == 0 then return #[]
    let params := ty.getAppArgs
    let mut out : Array Expr := #[]
    for ctorName in ii.ctors do
      let ctorApp := mkAppN (mkConst ctorName lvls) params
      -- the field telescope with parameters instantiated; a field depending
      -- on an earlier field has no rectangular product — skip the ctor
      let mut fieldTys : Array Expr := #[]
      let mut rectangular := true
      let mut rest ← whnf (← inferType ctorApp)
      while rest.isForall do
        if rest.bindingBody!.hasLooseBVar 0 then
          rectangular := false
          break
        fieldTys := fieldTys.push rest.bindingDomain!
        rest ← whnf rest.bindingBody!
      unless rectangular do continue
      let mut rows : Array (Array Expr) := #[#[]]
      for fty in fieldTys do
        let vals ← enumerateValues fty (depth - 1) cap
        let mut next : Array (Array Expr) := #[]
        for row in rows do
          for v in vals do
            if next.size < cap then next := next.push (row.push v)
        rows := next
      for row in rows do
        if out.size < cap then out := out.push (mkAppN ctorApp row)
    return out
  | _ => return #[]

/-- The result of a bounded search: the candidates that survived every
    checked hypothesis, and an honest account of what was checked. -/
public meta structure ModelSearch where
  /-- Candidates on which every checked hypothesis decided `true`. -/
  models : Array Expr := #[]
  /-- Candidates generated within the depth bound. -/
  candidates : Nat := 0
  /-- The enumeration hit `cap`: the count is a floor, not a total. -/
  capped : Bool := false
  /-- Hypotheses that decided on every candidate — these filtered. -/
  checked : Nat := 0
  /-- Hypotheses that could not be decided (no instance, or open in other
      variables) — these filtered nothing. -/
  unchecked : Nat := 0

/-- Search for values of the local variable `x` consistent with the
    hypotheses that mention it. A hypothesis filters only when it decides on
    *every* candidate; a single undecided substitution demotes it to
    unchecked, so the survivors never depend on a guess. -/
public meta def findModels (x : FVarId) (depth : Nat) (cap : Nat := 512) :
    MetaM ModelSearch := do
  let xe := mkFVar x
  let ty ← instantiateMVars (← x.getType)
  let cands ← enumerateValues ty depth cap
  let mut hyps : Array Expr := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if decl.fvarId == x then continue
    -- see through let aliases (`let y := x; h : y = true` mentions x only
    -- via y): unfold let-bound variables to their values before the mention
    -- check, so the substitution below reaches x
    let hypTy ← zetaReduce (← instantiateMVars decl.type)
    unless hypTy.containsFVar x do continue
    if ← Meta.isProp hypTy then
      hyps := hyps.push hypTy
  let mut surviving := cands
  let mut checked := 0
  let mut unchecked := 0
  for h in hyps do
    -- with no candidates left there is nothing to decide against: later
    -- hypotheses filtered nothing and count as unchecked, never as checked
    if surviving.isEmpty then
      unchecked := unchecked + 1
      continue
    let mut verdicts : Array (Expr × Bool) := #[]
    let mut decidesAll := true
    for v in surviving do
      match ← decideProp? (h.replaceFVar xe v) with
      | some b => verdicts := verdicts.push (v, b)
      | none => decidesAll := false; break
    if decidesAll then
      checked := checked + 1
      surviving := verdicts.filterMap fun (v, b) => if b then some v else none
    else
      unchecked := unchecked + 1
  return { models := surviving, candidates := cands.size,
           capped := cands.size ≥ cap, checked, unchecked }

end

end SpytialLean

module

meta import SpytialLean.ModelFind
meta import SpytialLean.InContext
meta import WalkCanon

open SpytialLean Lean Meta

/-! # Bounded model finding

`enumerateValues` counts, `findModels` filtering and honesty, and the
end-to-end walk with a found model injected as a refinement. -/

public inductive FTree where
  | leaf (value : Nat)
  | node (left right : FTree)
  deriving DecidableEq

private meta def fTree : Expr := .const ``FTree []

private meta def fLeaf (n : Nat) : Expr :=
  mkApp (mkConst ``FTree.leaf) (mkRawNatLit n)

/-! ## Enumeration is depth-bounded and constructor-wise -/

#eval show MetaM Unit from do
  -- depth 0: no constructor may be spent
  unless (← enumerateValues fTree 0).size == 0 do throwError "enum: depth 0"
  -- depth 1: leaf over Nat ≤ 0
  unless (← enumerateValues fTree 1).size == 1 do throwError "enum: depth 1"
  -- depth 2: leaf {0,1} + node over the one depth-1 tree
  unless (← enumerateValues fTree 2).size == 3 do throwError "enum: depth 2"
  -- depth 3: leaf {0,1,2} + node over the 3×3 depth-2 trees
  unless (← enumerateValues fTree 3).size == 12 do throwError "enum: depth 3"
  -- finite bases still come from tryEnumerateDomain
  unless (← enumerateValues (mkConst ``Bool) 0).size == 2 do throwError "enum: Bool"
  -- the cap is a hard ceiling
  unless (← enumerateValues fTree 4 (cap := 10)).size == 10 do throwError "enum: cap"

/-! ## Decidable hypotheses filter; open ones are unchecked, not assumed -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x fTree fun x => do
  withLocalDeclD `h (← mkAppM ``Ne #[x, fLeaf 0]) fun _ => do
    let search ← findModels x.fvarId! 2
    unless search.candidates == 3 do throwError "find: candidates {search.candidates}"
    unless search.models.size == 2 do throwError "find: models {search.models.size}"
    unless search.checked == 1 && search.unchecked == 0 do
      throwError "find: checked {search.checked}, unchecked {search.unchecked}"

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x fTree fun x => do
  withLocalDeclD `y fTree fun y => do
  -- `x = y` stays open after substituting x — no candidate is filtered
  withLocalDeclD `h (← mkAppM ``Eq #[x, y]) fun _ => do
    let search ← findModels x.fvarId! 2
    unless search.models.size == 3 do throwError "find.open: models {search.models.size}"
    unless search.checked == 0 && search.unchecked == 1 do
      throwError "find.open: checked {search.checked}, unchecked {search.unchecked}"

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x fTree fun x => do
  -- unsatisfiable within the bound: everything ruled out. h1 empties the
  -- pool, so h2 is never decided on anything — unchecked, not checked
  withLocalDeclD `h1 (← mkAppM ``Ne #[x, fLeaf 0]) fun _ => do
  withLocalDeclD `h2 (← mkAppM ``Eq #[x, fLeaf 0]) fun _ => do
    let search ← findModels x.fvarId! 1
    unless search.models.size == 0 do throwError "find.unsat: models {search.models.size}"
    unless search.checked == 1 && search.unchecked == 1 do
      throwError "find.unsat: checked {search.checked}, unchecked {search.unchecked}"

/-! ## A found model draws as the hole's structure

The `≠` that carved the search names a term not in the world, so it is
counted, not drawn: the diagram is the model, nothing else. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x fTree fun x => do
  withLocalDeclD `h (← mkAppM ``Ne #[x, fLeaf 0]) fun _ => do
    let search ← findModels x.fvarId! 2
    let some m := search.models[0]? | throwError "find.walk: no model"
    let cfg : WalkConfig :=
      { refinements := ({} : Std.HashMap FVarId Expr).insert x.fvarId! m }
    let (skipped, st) ← (walkInContext cfg x).run {}
    unless skipped == 1 do throwError "find.walk: skipped {skipped}"
    assertCanon "find.walk" st.toDataInstance
      "FTree|leaf\nNat|1\nvalue[FTree,Nat]:0,1"

/-! ## Honesty at the edges -/

-- an explicit large depth does not bypass the cap for Nat
#eval show Lean.Elab.TermElabM Unit from do
  let vals ← enumerateValues (mkConst ``Nat) 1000000 (cap := 8)
  unless vals.size == 8 do throwError "find.natCap: {vals.size} values"

-- once every candidate is ruled out, later hypotheses are never counted as
-- checked: there was nothing to decide them on
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Bool) fun x => do
  withLocalDeclD `h1 (← mkAppM ``Ne #[x, mkConst ``Bool.true]) fun _ => do
  withLocalDeclD `h2 (← mkAppM ``Ne #[x, mkConst ``Bool.false]) fun _ => do
  withLocalDeclD `R (← mkArrow (mkConst ``Bool) (mkSort Level.zero)) fun R => do
  withLocalDeclD `h3 (mkApp R x) fun _ => do
    let search ← findModels x.fvarId! 0
    unless search.models.isEmpty do throwError "find.exhausted: models"
    unless search.checked == 2 do throwError "find.exhausted: checked {search.checked}"
    unless search.unchecked == 1 do
      throwError "find.exhausted: unchecked {search.unchecked}"

-- a hypothesis reaching the subject only through a let alias still filters
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Bool) fun x => do
  withLetDecl `y (mkConst ``Bool) x fun y => do
  withLocalDeclD `h (← mkAppM ``Eq #[y, mkConst ``Bool.true]) fun _ => do
    let search ← findModels x.fvarId! 0
    unless search.checked == 1 do throwError "find.letAlias: checked {search.checked}"
    unless search.models.size == 1 do
      throwError "find.letAlias: {search.models.size} models"
    unless search.models[0]!.isConstOf ``Bool.true do
      throwError "find.letAlias: wrong model"

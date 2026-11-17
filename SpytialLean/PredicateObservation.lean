module

public meta import SpytialLean.LeanSelector
meta import Lean.Meta.Tactic.SolveByElim

namespace SpytialLean

open Lean Meta

/-- An observed predicate is an applied Lean term: its captured parameters are
fixed, and only its remaining arguments become columns. -/
public meta def predicateObservationName (predicate : Expr) : MetaM String := do
  return (← ppExpr predicate).pretty

private meta def predicateConstructors (predicate : Expr) : MetaM (List Name) := do
  forallTelescopeReducing (← inferType predicate) fun args _ => do
    let claim ← whnf (mkAppN predicate args)
    let .const name _ := claim.getAppFn | return []
    let some (.inductInfo info) := (← getEnv).find? name | return []
    return info.ctors

private meta def proveObservedTuple? (claim : Expr) (facts : PredicateEvidence)
    (constructors : List Name) : MetaM (Option Expr) := do
  if let some proof ← provePredicate? facts claim then return some proof
  if constructors.isEmpty then return none
  withoutModifyingState <| withNewMCtxDepth do
    let goal ← mkFreshExprSyntheticOpaqueMVar claim
    let rules : List (Elab.TermElabM Expr) :=
      (constructors ++ [``Eq.refl]).map fun name => liftM (mkConstWithFreshMVarLevels name)
    let known := facts.facts.toList.map (·.2)
    let solved ← observing? <| SolveByElim.solveByElim
      { maxDepth := 8, constructor := false, exfalso := false, intro := false, symm := false }
      rules (fun _ => pure known) [goal.mvarId!]
    unless solved == some [] do return none
    let proof ← instantiateMVars goal
    if proof.hasMVar then return none
    return some (← checkPredicateProof claim proof)

/-- Observe proof-backed membership over a fixed set of represented atoms.
Missing proofs leave tuples absent. Constructor search uses the retained
evidence, so an omitted local hypothesis cannot leak back into the picture. -/
public meta def observePredicates (ctx : LeanSelCtx) (predicates : Array Expr) :
    MetaM (JsonDataInstance × SelectorEvidence) := do
  if predicates.isEmpty then return (ctx.di, ctx.evidence)
  withoutModifyingState <| withNewMCtxDepth do
    let prepared ← preparePredicateEvidence ctx.evidence
    let mut data := ctx.di
    let mut evidence := ctx.evidence
    for (predicate, index) in predicates.zipIdx do
      let kind ← classifyLeanRel predicate
      unless kind.shape matches .pred true do
        throwError "predicate observation expects a proposition, got {← inferType predicate}"
      let columns ← kind.domains.mapM (predicateColumn ctx prepared)
      let types ← kind.domains.mapM sigOfType
      let name ← predicateObservationName predicate
      let headId ← headRelationId predicate.getAppFn types
      let captures ← dataArgsOf predicate
      -- Captures with the same pretty-printed name can be different local declarations.
      let id := if captures.isEmpty then headId else s!"{headId}:observed:{index}:{name}"
      let existing := data.relations.findIdx? (·.id == id)
      let relation : JsonRelation := match existing with
        | some i => { data.relations[i]! with name }
        | none => { id, name, types, tuples := #[] }
      let points := columns.foldl (fun n column => n * column.size) 1
      if points > 4096 then
        throwError "observing {name} would query {points} tuples; the limit is 4096"
      let constructors ← predicateConstructors predicate
      let rec visit (columns : List (Array (String × Expr))) (args : Array Expr)
          (ids : Array String) : StateT (JsonRelation × SelectorEvidence) MetaM Unit := do
        match columns with
        | col :: rest =>
          for (id, term) in col do visit rest (args.push term) (ids.push id)
        | [] =>
          if (← get).1.tuples.any (·.atoms == ids) then return
          let claim := mkAppN predicate args
          let some proof ← liftM (proveObservedTuple? claim prepared constructors) | return
          modify fun (rel, ev) => ({ rel with tuples := rel.tuples.push { atoms := ids, types } },
            { ev with proofs := ev.proofs.push proof })
      let (_, (observed, updatedEvidence)) ← (visit columns.toList #[] #[]).run (relation, evidence)
      evidence := updatedEvidence
      data := { data with relations := match existing with
        | some index => data.relations.set! index observed
        | none => data.relations.push observed }
    return (data, evidence)

end SpytialLean

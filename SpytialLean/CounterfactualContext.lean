module

public meta import SpytialLean.Context
public meta import SpytialLean.CounterfactualContext.HittingSets

/-! Counterfactual context preparation for a Lean inspection. The public result contains
    each observed conflict and the prepared evidence from each successful replay. The
    caller can project, draw or serialize those contexts using the ordinary inspection path. -/

namespace SpytialLean

open Lean Meta

public meta section

structure CounterfactualPreview where
  /-- Additional exclusions, in declaration order, for the displayed nvm clause. -/
  omitted : Array FVarId
  context : InspectionContext
  /-- The full configuration actually used to prepare this context. -/
  config : InspectionConfig := {}

structure ContradictionReport where
  /-- Free local hypotheses used by checked proofs of False, in declaration order. -/
  conflicts : Array (Array FVarId) := #[]
  previews : Array CounterfactualPreview := #[]
  limited : Bool := false

private structure SearchState where
  /-- All local proof sources for the explanation, including ones nvm cannot name. -/
  supports : Array (Array FVarId) := #[]
  /-- Only the source indices that nvm can omit participate in the hitting sets. -/
  hittingSets : CounterfactualContext.HittingSets := {}

/-- Record the local hypotheses in this particular proof. Remove administrative lets and
    unused lambda arguments while keeping named local proofs opaque. A proof subject is
    always admitted, and a shadowed or inaccessible binder cannot be named by nvm. -/
private def SearchState.recordConflict (state : SearchState) (subject proof : Expr)
    (excluded : Array FVarId) (candidateLimit : Nat) : MetaM SearchState := do
  let proof ← Core.betaReduce (← zetaReduce proof (zetaDelta := false))
  let used := (collectFVars {} proof).fvarSet
  let scope ← getLCtx
  let mut support := #[]
  let mut selectable := #[]
  for decl in scope do
    let id := decl.fvarId
    unless used.contains id && (← isProp decl.type) do continue
    support := support.push id
    if !excluded.contains id && !decl.isImplementationDetail && subject != mkFVar id &&
        !decl.userName.hasMacroScopes && (scope.findFromUserName? decl.userName).any (·.fvarId == id) then
      selectable := selectable.push decl.index
  let supports := if state.supports.contains support then state.supports else state.supports.push support
  return { supports, hittingSets := state.hittingSets.addConflict selectable candidateLimit }

/-- Start from the checked proof of False in the original inspection. Reiter's “A Theory of
    Diagnosis from First Principles”, Theorem 4.4, relates diagnoses to minimal hitting sets
    of conflicts. Here each recorded proof supplies a conflict and the selectable local
    hypotheses are the possible omissions. https://doi.org/10.1016/0004-3702(87)90062-2

    Each candidate is replayed with ordinary context preparation. A new proof refines the
    hitting sets. A successful replay supplies a displayable context. Minimality concerns
    the conflicts recorded by this search. Computing all semantic correction sets would
    additionally require deciding feasibility; see Liffiton et al., “Fast, Flexible MUS
    Enumeration”, §2. https://doi.org/10.1007/s10601-015-9183-0 -/
def inspectCounterfactuals (subject : Expr) (config : InspectionConfig) (firstProof : Expr)
    (maxReplays : Nat := 16) : MetaM ContradictionReport := do
  let scope ← getLCtx
  let candidateLimit := maxReplays + 1
  let mut state ← ({} : SearchState).recordConflict subject firstProof
    config.excludedHypotheses candidateLimit
  let mut successful : Array (Array Nat × CounterfactualPreview) := #[]
  for _ in [:maxReplays] do
    let some candidate := state.hittingSets.candidates.find? (fun ids => !successful.any (·.1 == ids))
      | break
    let omitted := candidate.filterMap fun i => (scope.getAt? i).map (·.fvarId)
    let replay := { config with excludedHypotheses := config.excludedHypotheses ++ omitted }
    let context ← prepareInspectionContext subject replay
    if let some proof := context.contradiction? then
      -- The new edge contains only sources still admitted on this replay. It is disjoint
      -- from this candidate, so adding the edge removes the candidate from the frontier.
      state ← state.recordConflict subject proof replay.excludedHypotheses candidateLimit
    else
      successful := successful.push (candidate, { omitted, context, config := replay })
  let previews := successful.filterMap fun (candidate, preview) =>
    if state.hittingSets.candidates.contains candidate then some preview else none
  let limited := state.hittingSets.limited || previews.size < state.hittingSets.candidates.size
  return { conflicts := state.supports, previews, limited }

end
end SpytialLean

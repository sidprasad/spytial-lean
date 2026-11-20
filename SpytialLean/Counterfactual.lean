module

public meta import SpytialLean.Context

namespace SpytialLean

open Lean Meta

public meta section

structure CounterfactualPreview where
  omitted : Array FVarId
  context : InspectionContext

structure ContradictionReport where
  /-- Free local hypotheses used by checked proofs of False, in declaration order. -/
  conflicts : Array (Array FVarId) := #[]
  previews : Array CounterfactualPreview := #[]
  limited : Bool := false

/-- The support of this particular proof, without temporary lets or unused lambda arguments
    introduced by automation. Named local proofs remain opaque evidence sources. -/
private def proofSources (proof : Expr) : MetaM (Array FVarId) := do
  let proof ← Core.betaReduce (← zetaReduce proof (zetaDelta := false))
  let used := (collectFVars {} proof).fvarSet
  let mut ids := #[]
  for decl in ← getLCtx do
    if used.contains decl.fvarId && (← isProp decl.type) then ids := ids.push decl.fvarId
  return ids

/-- Extend the previous minimal hitting sets by one newly discovered conflict. A removal is
    necessary precisely when some recorded conflict intersects the candidate only there. -/
private def extendOmissions (candidates : Array (Array Nat)) (conflicts : Array (Array Nat))
    (newConflict : Array Nat) (limit : Nat) : Array (Array Nat) × Bool := Id.run do
  let mut next := #[]
  for omitted in candidates do
    let extensions := if newConflict.any omitted.contains then #[omitted]
      else newConflict.map fun id => (omitted.push id).qsort (· < ·)
    for candidate in extensions do
      if next.contains candidate then continue
      if candidate.all fun id => conflicts.any fun conflict =>
          conflict.contains id && !(conflict.any fun j => j != id && candidate.contains j) then
        if next.size == limit then return (next, true)
        next := next.push candidate
  return (next, false)

/-- Replay actual nvm exclusions. A successful replay means the inspection found no
    contradiction. It is not a satisfiability oracle for Lean propositions. -/
def inspectCounterfactuals (subject : Expr) (config : InspectionConfig) (firstProof : Expr)
    (maxReplays : Nat := 16) : MetaM ContradictionReport := do
  let scope ← getLCtx
  let mut candidates : Array (Array Nat) := #[#[]]
  let mut conflicts : Array (Array Nat) := #[]
  let mut checked : Array (Array Nat × Option InspectionContext) := #[]
  let mut report : ContradictionReport := {}
  let mut pendingProof := some firstProof
  let mut replays := 0
  repeat
    let some omitted := candidates.find? (fun c => !(checked.any fun entry => entry.1 == c))
      | break
    let ids := omitted.filterMap fun i => (scope.getAt? i).map (·.fvarId)
    let excluded := config.excludedHypotheses ++ ids
    let proof ← match pendingProof with
      | some p => pure p
      | none => do
        if replays >= maxReplays then
          report := { report with limited := true }
          break
        replays := replays + 1
        let context ← prepareInspectionContext subject { config with excludedHypotheses := excluded }
        if let some proof := context.contradiction? then pure proof
        else
          checked := checked.push (omitted, some context)
          continue
    pendingProof := none
    checked := checked.push (omitted, none)
    let support ← proofSources proof
    if !report.conflicts.contains support then
      report := { report with conflicts := report.conflicts.push support }
    let mut selectable := #[]
    for id in support do
      let decl ← id.getDecl
      -- nvm accepts only a resolvable local identifier. A proof subject is itself
      -- admitted on every replay, and a shadowed binder cannot be named at this site.
      if !excluded.contains id && !decl.isImplementationDetail && subject != mkFVar id &&
          !decl.userName.hasMacroScopes && (scope.findFromUserName? decl.userName).any (·.fvarId == id) then
        selectable := selectable.push decl.index
    conflicts := conflicts.push selectable
    let (next, cut) := extendOmissions candidates conflicts selectable (maxReplays + 1)
    candidates := next
    report := { report with limited := report.limited || cut }
  for (candidate, context?) in checked do
    let some context := context? | continue
    if candidates.contains candidate then
      let omitted := candidate.filterMap fun i => (scope.getAt? i).map (·.fvarId)
      report := { report with previews := report.previews.push { omitted, context } }
  return report

end
end SpytialLean

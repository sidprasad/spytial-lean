import Lean
import SpytialLean.CounterfactualContext
import SpytialLean.CounterfactualContext.HittingSets

open Lean Meta Elab Tactic SpytialLean SpytialLean.CounterfactualContext

set_option linter.unusedVariables false

private def subsets (xs : Array α) : Array (Array α) :=
  xs.foldl (fun acc x => acc ++ acc.map (·.push x)) #[#[]]

-- Compare the incremental update to the definition: keep each hitting set that has
-- no strict hitting subset. Include the empty family and the empty conflict.
private def agreesWithEnumeration (edges allSubsets : Array (Array Nat)) : Bool := Id.run do
  let hits := allSubsets.filter fun candidate => edges.all fun edge => edge.any candidate.contains
  let minimal := hits.filter fun candidate =>
    !(hits.any fun smaller => smaller.size < candidate.size && smaller.all candidate.contains)
  let actual := edges.foldl (fun sets edge => sets.addConflict edge allSubsets.size) ({} : HittingSets)
  return !actual.limited && actual.candidates.size == minimal.size && minimal.all actual.candidates.contains

#guard Id.run do
  let allSubsets := subsets #[0, 1, 2]
  return (subsets allSubsets).all fun edges =>
    agreesWithEnumeration edges allSubsets && agreesWithEnumeration edges.reverse allSubsets

-- Reaching the limit exactly is fine. Actually dropping a candidate permanently marks
-- the search as incomplete, even if a later conflict eliminates every retained option.
#guard Id.run do
  let empty : HittingSets := {}
  let exact := empty.addConflict #[0, 1] 2
  let cut := empty.addConflict #[0, 1] 1
  let impossible := cut.addConflict #[] 1
  return !exact.limited && exact.candidates == #[#[0], #[1]] &&
    cut.limited && cut.candidates == #[#[0]] && impossible.limited && impossible.candidates.isEmpty

-- Two overlapping conflicts have two minimal omissions, of different sizes. A second
-- independent conflict must also be hit in every successful replay.
elab "check_counterfactuals " root:term : tactic => withMainContext do
  let root ← Term.elabTerm root none
  let config : InspectionConfig := { simplify := true }
  let some proof := (← prepareInspectionContext root config).contradiction?
    | throwError "expected a contradiction"
  let report ← inspectCounterfactuals root config proof
  let omissions ← report.previews.mapM fun p => p.omitted.mapM (·.getUserName)
  let expected := #[#[`hp, `bad], #[`hn, `hn', `bad]]
  unless !report.limited && omissions.size == expected.size && expected.all omissions.contains do
    throwError "unexpected counterfactuals {omissions}"
  let bounded ← inspectCounterfactuals root config proof (maxReplays := 0)
  unless bounded.limited && bounded.previews.isEmpty && bounded.conflicts.size == 1 do
    throwError "the replay bound hid the original explanation or advertised an untested preview"

example (x : Nat) (hp : x = 3) (hn hn' : x ≠ 3) (bad : False) : True := by
  check_counterfactuals x
  trivial

module

public import Lean
public meta import SpytialLean.SpecLang

open SpytialLean.SpecLang Lean

/-! # Coverage — the surface spytial-core has deprecated

`SpecLang.lean` drops every deprecated item and field while it derives the
tables, so a *live* op would leave with no notice past `unknown Spytial op` at
a call site. The pins below fail instead, naming it and its replacement. -/

private meta def pinnedItems : List (String × String) :=
  [("icon", "atomStyle"), ("atomColor", "atomStyle"), ("edgeColor", "edgeStyle")]

private meta def pinnedFields : List (String × String) :=
  [("inferredEdge.color", "lineStyle.color"),
   ("inferredEdge.style", "lineStyle.pattern"),
   ("inferredEdge.weight", "lineStyle.weight"),
   ("inferredEdge.highlight", "lineStyle.highlight")]

private meta def account (what : String) (pinned live : List (String × String)) :
    Array String := Id.run do
  let mut problems : Array String := #[]
  for (name, replacedBy) in live do
    match pinned.lookup name with
    | none =>
      problems := problems.push s!"core deprecated the {what} '{name}' in favour \
        of '{replacedBy}', so this rebuild drops it from the surface"
    | some want =>
      unless want == replacedBy do
        problems := problems.push
          s!"the {what} '{name}' is replaced by '{replacedBy}' now, not '{want}'"
  for (name, _) in pinned do
    unless live.any (·.1 == name) do
      problems := problems.push
        s!"the {what} '{name}' is pinned here, but the manifest does not deprecate it"
  return problems

private meta def report : Elab.Command.CommandElabM Unit := do
  let problems := account "item" pinnedItems deprecatedItems
    ++ account "field" pinnedFields deprecatedFields
  unless problems.isEmpty do
    throwError "the declined surface is out of date ({problems.size}):\n{
      "\n".intercalate problems.toList}"
  logInfo m!"{pinnedItems.length} items and {pinnedFields.length} fields declined"

/-- info: 3 items and 4 fields declined -/
#guard_msgs in
run_cmd report

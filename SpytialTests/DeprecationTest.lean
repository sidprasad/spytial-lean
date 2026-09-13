module

public import Lean
public meta import SpytialLean.SpecLang

open SpytialLean.SpecLang Lean

/-! # Coverage — the surface spytial-core has deprecated

`SpecLang.lean` drops every deprecated item and field while it derives the
tables, so the Lean surface never spells one. That is deliberate: the DSL is
new and has no legacy specs to keep parsing.

It is also how a *live* op would leave. Core marks it deprecated, the next
rebuild drops it, and the first anyone hears is `unknown Spytial op` at a call
site that says nothing about what replaced it. So the account is pinned below,
and an item or field core deprecates that is not on it fails here instead,
naming it and its replacement.
-/

private meta def pinnedItems : List (String × String) :=
  [("icon", "atomStyle"), ("atomColor", "atomStyle"), ("edgeColor", "edgeStyle")]

private meta def pinnedFields : List (String × String) :=
  [("inferredEdge.color", "lineStyle.color"),
   ("inferredEdge.style", "lineStyle.pattern"),
   ("inferredEdge.weight", "lineStyle.weight"),
   ("inferredEdge.highlight", "lineStyle.highlight")]

/-- Both directions: what the manifest deprecates and the pins do not account
    for, and what the pins claim and the manifest no longer says. -/
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

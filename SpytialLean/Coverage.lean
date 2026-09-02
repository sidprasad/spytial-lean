module

public import Lean
public import Lean.Elab.Command
public meta import SpytialLean.Attr
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Elab Command Meta

/-! # Build-time coverage checking

Checks that every `Type`-valued inductive and structure of a namespace has a
spec, a custom relationalizer, or an explicit opt-out. `Prop`-valued inductives
are excluded — their elements are proofs, a separate `#spytial.proof` concern —
and so are type classes. -/

public section

/-- Data, meaning `Type`-valued rather than `Prop`-valued. -/
meta def isDataType (ii : InductiveVal) : MetaM Bool :=
  forallTelescopeReducing ii.type fun _ body => return !body.isProp

/-- Module-private types are name-mangled to `_private.…`, both an internal
    detail and outside `root`'s prefix, so they are never enumerated. -/
meta def coverageReport (root : Name) : MetaM (Array (Name × Bool)) := do
  let env ← getEnv
  -- Pure name filter first; the MetaM refinement runs only on survivors.
  let candidates : Array (Name × InductiveVal) := env.constants.fold (init := #[])
    fun acc n ci =>
      match ci with
      | .inductInfo ii =>
        if root.isPrefixOf n && !n.isInternalDetail && !n.hasMacroScopes
            && !isClass env n then
          acc.push (n, ii)
        else acc
      | _ => acc
  let mut out : Array (Name × Bool) := #[]
  for (n, ii) in candidates do
    unless (← isDataType ii) do continue
    let directlyCovered := (getSpytialSpec? env n).isSome || (getSpytialOptOut? env n).isSome
      || (getSpytialRelationalizerName? env n).isSome
    -- Mirrors `lookupTypeSpec`'s parent walk. Specs inherit; relationalizers
    -- and opt-outs do not.
    let covered ← do
      if directlyCovered || !isStructure env n then
        pure directlyCovered
      else
        let parents ← getAllParentStructures n
        pure (parents.any (getSpytialSpec? env · |>.isSome))
    out := out.push (n, covered)
  return out

/-- `spytial_opt_out <Decl> ["reason"]` waives a type from the coverage check,
    so it counts as covered despite having no spec. -/
syntax (name := spytialOptOutCmd) "spytial_opt_out " ident (str)? : command

@[command_elab spytialOptOutCmd]
meta def elabSpytialOptOutCmd : CommandElab := fun
  | `(spytial_opt_out $id:ident $[$reason?:str]?) => do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let reason := (reason?.map (·.getString)).getD ""
    liftCoreM <| setSpytialOptOut declName reason
  | stx => throwError "Unexpected syntax {stx}."

/-- Only the `!` form gates a build by itself; the plain form warns, which fails
    a build only under `warningAsError`. -/
syntax (name := spytialCoverageCmd) "#spytial.coverage" "!"? ident : command

@[command_elab spytialCoverageCmd]
meta def elabSpytialCoverageCmd : CommandElab := fun stx => do
  let strict := !stx[1].isNone
  let root := stx[2].getId
  let report ← liftTermElabM <| coverageReport root
  let total := report.size
  let covered := (report.filter (·.2)).size
  let uncovered := (report.filterMap fun (n, c) => if c then none else some n)
    |>.qsort (fun a b => decide (toString a < toString b))
  if total == 0 then
    -- 0/0 must not pass as covered: the root may be mistyped or unimported.
    let msg := m!"no Spytial coverage data types found under '{root}' — check the \
      spelling and that the namespace is imported"
    if strict then throwError msg else logWarning msg
  else if uncovered.isEmpty then
    logInfo m!"Spytial coverage: {covered}/{total} data types in '{root}' covered."
  else
    let listing := String.intercalate "\n" (uncovered.toList.map fun n => s!"  • {n}")
    let msg := m!"Spytial coverage for '{root}': {covered}/{total} covered, \
      {uncovered.size} uncovered:\n{listing}\n\
      Attach a spec with `spytial_spec <Name> [...]`, register a custom \
      relationalizer with `spytial_relationalizer`, or waive with \
      `spytial_opt_out <Name> \"reason\"`."
    if strict then throwError msg else logWarning msg

end

end SpytialLean

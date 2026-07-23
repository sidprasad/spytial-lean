module

public import Lean
public import Lean.Elab.Command
public meta import SpytialLean.Attr
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Elab Command Meta

/-! # Build-time coverage checking

Enumerates the visualizable *data* types of a namespace — `Type`-valued inductives
and structures — and checks that each either has an attached Spytial spec
(`spytial_spec`), a registered custom relationalizer (`spytial_relationalizer`), or
an explicit opt-out (`spytial_opt_out`). Run from a module that is part of
`lake build`, so that as the upstream library evolves any newly added type without
a spec surfaces as a build-time warning — or, in strict mode, an error that fails
the build.

`Prop`-valued inductives (judgments/relations) are excluded: their elements are
proofs, which are a separate `#spytial.proof` concern, not data diagrams. Type
classes are likewise excluded — interfaces to implement, not data to diagram.

Registration names resolve like ordinary identifiers (relative to the current
namespace and any `open`s), and entries are keyed by the resolved fully-qualified
name — the same form the enumeration produces. -/

public section

/-- Whether an inductive's elements are data (`Type`-valued) rather than proofs
    (`Prop`-valued). -/
meta def isDataType (ii : InductiveVal) : MetaM Bool :=
  forallTelescopeReducing ii.type fun _ body => return !body.isProp

/-- The coverage candidates in `root`, each paired with whether it is covered (has an
    attached spec, a custom relationalizer, or an explicit opt-out).

    Non-public (module-private) types are name-mangled to `_private.…` — both an
    internal detail and outside `root`'s prefix — so they are not enumerated. -/
meta def coverageReport (root : Name) : MetaM (Array (Name × Bool)) := do
  let env ← getEnv
  -- cheap pure name filter first; the MetaM refinement below runs only on survivors
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
    -- A structure also renders — and so counts — via an inherited spec, mirroring
    -- `lookupTypeSpec`'s parent walk (Command.lean). Spec inheritance only:
    -- relationalizers and opt-outs do not inherit.
    let covered ← do
      if directlyCovered || !isStructure env n then
        pure directlyCovered
      else
        let parents ← getAllParentStructures n
        pure (parents.any (getSpytialSpec? env · |>.isSome))
    out := out.push (n, covered)
  return out

/-! ## spytial_opt_out command -/

/-- `spytial_opt_out <Decl> ["reason"]` waives a type from the Spytial coverage
    check, so it counts as covered despite having no spec. -/
syntax (name := spytialOptOutCmd) "spytial_opt_out " ident (str)? : command

@[command_elab spytialOptOutCmd]
meta def elabSpytialOptOutCmd : CommandElab := fun
  | `(spytial_opt_out $id:ident $[$reason?:str]?) => do
    let declName ← resolveGlobalConstNoOverload id
    let reason := (reason?.map (·.getString)).getD ""
    liftCoreM <| setSpytialOptOut declName reason
  | stx => throwError "Unexpected syntax {stx}."

/-! ## #spytial.coverage command -/

/-- `#spytial.coverage <Namespace>` reports Spytial spec coverage over the
    `Type`-valued inductives/structures in `<Namespace>`, warning on any gaps.

    `#spytial.coverage! <Namespace>` is strict: it errors on gaps, failing the
    build. Place such a command in a module imported by the build target, after all
    `spytial_spec`/`spytial_opt_out` declarations.

    Only the `!` form gates a build; the plain form only ever warns (nothing here
    promotes its warning to an error), so it reports but cannot fail CI. -/
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
    -- Nothing matched the root: a mistyped, renamed, or unimported namespace
    -- must not silently pass — reporting 0/0 as "covered" is a false gate.
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

module

public import Lean
public meta import Lean.Elab.Declaration
public meta import SpytialLean.Widget

namespace SpytialLean

open Lean Elab Command Widget

public meta section

/-- A transient, environment-owned journal: tactic backtracking restores it,
    unlike diagnostic info trees which deliberately retain failed alternatives.
    It is cleared after each declaration and is never serialized into imports. -/
initialize inspectionJournal : EnvExtension (Option (Array (Syntax × Json))) ←
  registerEnvExtension (pure none)

def recordInspection (stx : Syntax) (props : Json) : CoreM Unit :=
  modifyEnv fun env => inspectionJournal.modifyState env (·.map (·.push (stx, props)))

private partial def hasInspection (stx : Syntax) : Bool :=
  stx.isOfKind `SpytialLean.spytialTactic || stx.getArgs.any hasInspection

/-- Keep Lean's declaration elaboration, then attach the retained proof inspections
    to its name. The ordinary tactic widgets stay at their original source spans. -/
@[command_elab Lean.Parser.Command.declaration]
def elabInspectionDeclaration : CommandElab := fun stx => do
  let decl := stx[1]
  unless decl.isOfKind ``Lean.Parser.Command.theorem ||
      decl.isOfKind ``Lean.Parser.Command.definition do throwUnsupportedSyntax
  unless hasInspection decl do throwUnsupportedSyntax
  -- Inspection-bearing declarations finish their proof before collecting its
  -- widgets. Ordinary declarations fall through to Lean's incremental/async
  -- elaborator above. No shared mutable registry crosses tasks or edits.
  let saved := inspectionJournal.getState (← getEnv)
  modifyEnv fun env => inspectionJournal.setState env (some #[])
  try
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) <|
      Lean.Elab.Command.elabDeclaration stx
    let points := (inspectionJournal.getState (← getEnv)).getD #[]
    let points := points.qsort fun a b => a.1.getPos?.getD 0 < b.1.getPos?.getD 0
    if points.isEmpty then return
    liftCoreM <| savePanelWidgetInfo SpytialWidget.javascriptHash (return Json.mkObj [
      ("explorer", Json.mkObj [
        ("name", toJson (expandDeclIdCore decl[1]).1.toString),
        ("points", toJson (points.map (·.2)))])]) decl[1]
  finally
    modifyEnv fun env => inspectionJournal.setState env saved

end

end SpytialLean

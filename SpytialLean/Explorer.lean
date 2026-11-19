module

public import Lean
public meta import Lean.Elab.Declaration
public meta import SpytialLean.Widget

namespace SpytialLean

open Lean Elab Command Widget

public meta section

structure InspectionJournal where
  declaration : Syntax
  points : Array (Syntax × Json) := #[]
  propositions : Std.HashMap Expr Nat := {}
  deriving Inhabited

/-- A transient, environment-owned journal: tactic backtracking restores it,
    unlike diagnostic info trees which deliberately retain failed alternatives.
    It is cleared after each declaration and is never serialized into imports. -/
initialize inspectionJournal : EnvExtension (Option InspectionJournal) ←
  -- A macro can introduce an inspection after `hasInspection` has run, in an async declaration.
  -- Its absent journal must still support the no-op update in `recordInspection`.
  registerEnvExtension (pure none) (asyncMode := .local)

/-- Compare propositions across this declaration's points using Lean expressions.
    Two branches can print the same local name for different free variables. -/
def inspectionFactIds? (facts : Array Expr) : CoreM (Option (Array Nat)) := do
  let some journal := inspectionJournal.getState (← getEnv) | return none
  let mut propositions := journal.propositions
  let mut ids := #[]
  for fact in facts do
    if let some id := propositions[fact]? then
      ids := ids.push id
    else
      let id := propositions.size
      propositions := propositions.insert fact id
      ids := ids.push id
  modifyEnv fun env => inspectionJournal.setState env (some { journal with propositions })
  return some ids

def recordInspection (stx : Syntax) (props : Json) : CoreM Unit :=
  modifyEnv fun env => inspectionJournal.modifyState env fun current => current.map fun journal =>
    { journal with points := journal.points.push (stx, props) }

/-- The enclosing source branch delimits term comparisons. An unlocated or generated site
    has no comparison scope. Lean's free-variable identities still decide every atom match. -/
private def termScope? (decl site : Syntax) : Option String := do
  let range ← site.getRange?
  let stack ← decl.findStack? (fun s => s.getRange?.any fun r => r.includes range) fun s =>
    s.isOfKind `SpytialLean.spytialTerm && s.getRange? == some range
  let region := stack.findSome? fun (s, i) =>
    if s.isOfKind ``Parser.Term.matchAlt then some s
    else if [``termIfThenElse, ``termDepIfThenElse, ``termIfLet, ``boolIfThenElse].contains s.getKind
      then some s[i]
    -- Tactic and do notation can introduce branches of their own.
    else if s.isOfKind ``Parser.Term.byTactic || s.isOfKind ``Parser.Term.«do» then some site
    else none
  let pos ← (region.getD decl).getPos?
  return s!"term:{pos.byteIdx}"

def termInspectionScope (site : Syntax) : CoreM String := do
  let journal? := inspectionJournal.getState (← getEnv)
  return (journal?.bind fun j => termScope? j.declaration site).getD ""

private partial def hasInspection (stx : Syntax) : Bool :=
  stx.isOfKind `SpytialLean.spytialTactic || stx.isOfKind `SpytialLean.spytialTerm ||
    stx.getArgs.any hasInspection

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
  modifyEnv fun env => inspectionJournal.setState env (some { declaration := decl })
  try
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) <|
      Lean.Elab.Command.elabDeclaration stx
    let points := (inspectionJournal.getState (← getEnv)).map (·.points) |>.getD #[]
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

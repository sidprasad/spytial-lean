module

public import Lean
public import Lean.Elab.Command
public meta import SpytialLean.Command

namespace SpytialLean

open Lean Elab Command

public section

/-- `cases/` beside the invoking source file, so the dump location doesn't
    depend on cwd. -/
private meta def casesDir : CommandElabM System.FilePath := do
  let src := System.FilePath.mk (← getFileName)
  return (src.parent.getD ".") / "cases"

/-- Atom/relation counts for the dump log, read back out of the props JSON. -/
private meta def instanceStats (props : Json) : String :=
  ((do
    let di ← props.getObjVal? "dataInstance"
    let atoms ← (← di.getObjVal? "atoms").getArr?
    let rels ← (← di.getObjVal? "relations").getArr?
    pure s!"{atoms.size} atoms, {rels.size} relations") : Except String String)
  |>.toOption.getD "unreadable props"

/-- `#spytial_snapshot "<name>" <term> (with [<ops>])?` writes the widget props
    for `<term>` — the JSON `#spytial` hands the infoview, via
    `spytialPayloadProps` — to `cases/<name>/props.json` beside the invoking
    file. `render/render.mjs` turns dumps into PNGs; see `render/README.md`. -/
syntax (name := snapshotCmd)
  "#spytial_snapshot " str ppSpace term (" with " "[" spytial_op,* "]")? : command

private meta def dumpSnapshot (name : TSyntax `str) (t : Syntax)
    (ops? : Option (Array (TSyntax `spytial_op))) : CommandElabM Unit := do
  let props ← liftTermElabM <| spytialPayloadProps t ops?
  let dir := (← casesDir) / name.getString
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "props.json") (props.pretty ++ "\n")
  logInfo m!"snapshot case '{name.getString}': {instanceStats props}"

@[command_elab snapshotCmd]
meta def elabSnapshot : CommandElab := fun
  | `(#spytial_snapshot $name:str $t:term) => dumpSnapshot name t none
  | `(#spytial_snapshot $name:str $t:term with [$ops,*]) => dumpSnapshot name t (some ops.getElems)
  | stx => throwError "Unexpected syntax {stx}."

end

end SpytialLean

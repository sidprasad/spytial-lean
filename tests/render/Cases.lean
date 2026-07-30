import SpytialLean
import Showcase

/-! # Render-test case dumper

`#spytial_snapshot "<name>" <term> (with <ops>)?` writes `cases/<name>/props.json`
for `render.spec.mjs` to screenshot and diff. The props come from
`spytialPayloadProps`, so a case cannot drift from what the infoview receives.

Run via `just render`. Deliberately a plain (non-`module`) file, like the demos,
so it can use the library's meta surface without module-system ceremony.
-/

open Lean Elab Command SpytialLean

syntax (name := snapshotCmd)
  "#spytial_snapshot " str ppSpace term (" with " term)? : command

/-- `cases/` beside this source file, so the dump location doesn't depend on cwd. -/
private def casesDir : CommandElabM System.FilePath := do
  let src := System.FilePath.mk (← getFileName)
  return (src.parent.getD ".") / "cases"

/-- Atom/relation counts for the dump log, read back out of the props JSON. -/
private def instanceStats (props : Json) : String :=
  ((do
    let di ← props.getObjVal? "dataInstance"
    let atoms ← (← di.getObjVal? "atoms").getArr?
    let rels ← (← di.getObjVal? "relations").getArr?
    pure s!"{atoms.size} atoms, {rels.size} relations") : Except String String)
  |>.toOption.getD "unreadable props"

@[command_elab snapshotCmd]
def elabSnapshot : CommandElab := fun
  | `(#spytial_snapshot $name:str $t:term $[with $spec?]?) => do
    let props ← liftTermElabM <| spytialPayloadProps t (spec?.map (·.raw))
    let dir := (← casesDir) / name.getString
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "props.json") (props.pretty ++ "\n")
    logInfo m!"snapshot case '{name.getString}': {instanceStats props}"
  | stx => throwError "Unexpected syntax {stx}."

/-! ## Cases

One per distinct visual feature. Values and specs come from the demos, so these
snapshots track what a user of the demo files actually sees.
-/

-- Red-black tree: nil-hiding, key/color attributes, node coloring by field label.
#spytial_snapshot "rbtree" exampleRBTree

-- Attached polymorphic-type spec (lenient scope).
#spytial_snapshot "tree" myTree

-- Inline `with` override of an attached spec.
#spytial_snapshot "tree-inline" myTree with [
  .orientation (selector := "left") (directions := [.above]),
  .orientation (selector := "right") (directions := [.above]),
  .atomColor (selector := "Tree") (value := "#0066ff"),
  .hideAtom (selector := "Nat")
]

-- Structure with attribute ops only (no constraints).
#spytial_snapshot "person" alice with [
  .attribute (field := "name"),
  .attribute (field := "age"),
  .atomColor (selector := "Person") (value := "#4CAF50")
]

-- Spec inheritance: Vehicle ops ++ ElectricCar ops.
#spytial_snapshot "ev" myEV

-- Plain list, scalar atoms hidden.
#spytial_snapshot "list" myList with [
  .hideAtom (selector := "Nat")
]

-- No spec at all (Person has none attached): the `cndSpec` prop is absent,
-- exercising the widget's free-layout path.
#spytial_snapshot "person-free" alice

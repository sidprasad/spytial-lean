import SpytialLean
import Showcase

/-! # Render-test case dumper

`#spytial_snapshot "<name>" <term> (with [...])?` writes
`tests/render/cases/<name>/props.json` — byte-identical to the props object the
infoview widget receives from `#spytial` — for the headless render harness
(`tests/render/render.spec.mjs`) to screenshot and diff.

Run from the repo root: `lake env lean tests/render/Cases.lean`.
This file is deliberately a plain (non-`module`) file, like the demos, so it
can use the library's meta surface without module-system ceremony.
-/

open Lean Elab Command SpytialLean

syntax (name := snapshotCmd)
  "#spytial_snapshot " str ppSpace term (" with " "[" spytial_op,* "]")? : command

/-- Atom/relation counts for the dump log, read back out of the props JSON
    (`spytialPayloadProps` is the public surface; its pieces are private). -/
private def instanceStats (props : Json) : String :=
  ((do
    let di ← props.getObjVal? "dataInstance"
    let atoms ← (← di.getObjVal? "atoms").getArr?
    let rels ← (← di.getObjVal? "relations").getArr?
    pure s!"{atoms.size} atoms, {rels.size} relations") : Except String String)
  |>.toOption.getD "unreadable props"

@[command_elab snapshotCmd]
def elabSnapshot : CommandElab := fun stx => do
  let some name := stx[1].isStrLit? | throwErrorAt stx[1] "expected string literal"
  let ops? : Option (Array (TSyntax `spytial_op)) :=
    if stx[3].getNumArgs == 0 then none
    else some (stx[3][2].getSepArgs.map (⟨·⟩))
  let props ← liftTermElabM <| spytialPayloadProps stx[2] ops?
  let dir := System.FilePath.mk "tests/render/cases" / name
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "props.json") (props.pretty ++ "\n")
  logInfo m!"snapshot case '{name}': {instanceStats props}"

/-! ## Cases

One per distinct visual feature. Values and specs come from the demos, so these
snapshots track what a user of the demo files actually sees (exception:
`group-align`, below).

The flagship BDD cases (`bdd`, `bdd-reduced`) return with the identity PR —
the demo and its collapse machinery aren't in this series yet.
-/

-- Red-black tree: nil-hiding, key/color attributes, node coloring by field label.
#spytial_snapshot "rbtree" exampleRBTree

-- Attached polymorphic-type spec (lenient scope).
#spytial_snapshot "tree" myTree

-- Inline `with` override of an attached spec.
#spytial_snapshot "tree-inline" myTree with [
  orientation left above,
  orientation right above,
  atomColor Tree "#0066ff",
  hideAtom Nat
]

-- Structure with attribute ops only (no constraints).
#spytial_snapshot "person" alice with [
  attribute name,
  attribute age,
  atomColor Person "#4CAF50"
]

-- Spec inheritance: Vehicle ops ++ ElectricCar ops.
#spytial_snapshot "ev" myEV

-- Plain list, scalar atoms hidden.
#spytial_snapshot "list" myList with [
  hideAtom Nat
]

-- No spec at all (Person has none attached): the `cndSpec` prop is absent,
-- exercising the widget's free-layout path.
#spytial_snapshot "person-free" alice

/-- Purpose-built (not from a demo): interim coverage for the visual features
    the BDD cases carried — group boxes, align, per-field edge colors — until
    the identity PR brings those demos back. -/
structure TreePair where
  left : Tree Nat
  right : Tree Nat

def duo : TreePair := { left := .node (.leaf 1) (.leaf 2), right := .leaf 3 }

#spytial_snapshot "group-align" duo with [
  group Tree grove,
  align {x, y : Tree | x != y} horizontal,
  edgeColor left "#e91e63",
  edgeColor right "#0066ff",
  hideAtom Nat
]

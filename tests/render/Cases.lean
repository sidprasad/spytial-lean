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

The payload assembly below duplicates `#spytial`'s, because the last step
(`elabSpytialPayload`, `spytialProps`) is private to `SpytialLean.Command` and
there is no public payload entry point yet. It converges onto one as the
library grows it.
-/

open Lean Elab Command Term Meta SpytialLean

syntax (name := snapshotCmd)
  "#spytial_snapshot " str ppSpace term (" with " "[" spytial_op,* "]")? : command

/-- The widget props for a term plus optional inline ops, exactly as `#spytial`
    builds them: explicit ops override an attached spec. -/
private def snapshotProps (t : Syntax) (ops? : Option (Array (TSyntax `spytial_op))) :
    TermElabM Json := do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let di ← relationalize e
  let spec? ← match ops? with
    | some ops => some <$> elabSpytialOps (← scopeForExpr e) ops
    | none => lookupTypeSpec e
  return Json.mkObj <|
    [("dataInstance", toJson di)] ++
    match spec? with
    | some s => [("cndSpec", toJson s.toYaml)]
    | none => []

/-- Atom/relation counts for the dump log, read back out of the props JSON. -/
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
  let props ← liftTermElabM <| snapshotProps stx[2] ops?
  let dir := System.FilePath.mk "tests/render/cases" / name
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "props.json") (props.pretty ++ "\n")
  logInfo m!"snapshot case '{name}': {instanceStats props}"

/-! ## Cases

One per distinct visual feature. Values and specs come from the demos, so these
snapshots track what a user of the demo files actually sees.

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

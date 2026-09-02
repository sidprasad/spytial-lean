module

public meta import SpytialLean.Relationalizer

open SpytialLean Lean

/-- Two walks allocate different atom ids but emit surviving atoms in the same
DFS order, so renaming ids by array position makes their instances comparable.
Relations arrive in hash order, hence the sort. -/
public meta def canonInstance (di : JsonDataInstance) : String := Id.run do
  let mut idx : Std.HashMap String Nat := {}
  for a in di.atoms do
    idx := idx.insert a.id idx.size
  let atomsS := di.atoms.map fun a => s!"{a.type}|{a.label}"
  let rels := di.relations.qsort (·.name < ·.name)
  let relsS := rels.map fun r =>
    let ts := r.tuples.map fun t =>
      String.intercalate "," (t.atoms.map (fun a => toString (idx.getD a 9999))).toList
    s!"{r.name}[{String.intercalate "," r.types.toList}]:{String.intercalate ";" ts.toList}"
  return String.intercalate "\n" (atomsS ++ relsS).toList

/-- `Foo.lean:12` → `Foo.lean:N`: the stamp's line moves whenever the lines
    above it do, so the goldens pin the file, never the line. -/
public meta def maskLines (s : String) : String :=
  match s.splitOn ".lean:" with
  | [] => s
  | first :: rest =>
    first ++ String.join (rest.map fun part =>
      ".lean:N" ++ (part.dropWhile Char.isDigit).toString)

public meta def assertCanon (label : String) (di : JsonDataInstance) (expected : String) :
    MetaM Unit := do
  let got := canonInstance di
  unless got == expected do
    throwError "{label}: canon mismatch\n-- got --\n{got}\n-- expected --\n{expected}"

public meta def assertMatchesReference (label : String) (e : Expr) (cfg : WalkConfig := {}) :
    MetaM Unit := withoutModifyingEnv do
  -- `walkExpr`/`referenceRelationalize` skip `relationalize`'s rollback, so
  -- without this the oracle runs under an environment the commands never see.
  let (rootF, stF) ← (walkExpr cfg e).run {}
  let diF := stF.toDataInstance
  let (rootR, diR) ← referenceRelationalize e cfg
  let cF := canonInstance diF
  let cR := canonInstance diR
  unless cF == cR do
    throwError "{label}: fused ≠ reference\n-- fused --\n{cF}\n-- reference --\n{cR}"
  let idxOf (di : JsonDataInstance) (id : String) : Option Nat :=
    di.atoms.findIdx? (·.id == id)
  unless idxOf diF rootF == idxOf diR rootR do
    throwError "{label}: root atoms disagree"

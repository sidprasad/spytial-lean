module

public meta import SpytialLean.Relationalizer

open SpytialLean Lean

/-! ## Canonical comparison

Two walks allocate different atom ids but emit surviving atoms in the same DFS
order, so renaming ids by atoms-array position makes their instances directly
comparable. Relations are sorted by name (the state stores them in hash order)
and carry their declared column types. -/

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

/-- Exact-shape golden: the whole canonical form, so a change anywhere in the
    emission fails the test. -/
public meta def assertCanon (label : String) (di : JsonDataInstance) (expected : String) :
    MetaM Unit := do
  let got := canonInstance di
  unless got == expected do
    throwError "{label}: canon mismatch\n-- got --\n{got}\n-- expected --\n{expected}"

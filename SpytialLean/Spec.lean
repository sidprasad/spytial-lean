module

public import Lean
public meta import SpytialLean.SpecGenerated

namespace SpytialLean

/-! The op type, its enums and style blocks, and the per-op serialization all
live in `SpytialLean.SpecGenerated`, generated from spytial-core's language
manifest (`just gen-spec`). This module is the hand-written residue: the spec
list type, the two-section document assembly, and merging. -/

/-- `LinePattern` under the name the pre-4.x surface used. -/
@[deprecated LinePattern (since := "2026-08-03")]
public meta abbrev EdgeStyle := LinePattern

/-- A list of Spytial operations forming a complete layout specification. -/
public meta abbrev SpytialSpec := List SpytialOp

/-! ## YAML serialization

`parseLayoutSpec` in spytial-core accepts YAML with two top-level keys:
```yaml
constraints:
  - orientation: {selector: "...", directions: [above, below]}
directives:
  - atomStyle: {selector: "...", fillStyle: {color: "#ff0000"}}
```
We partition `SpytialOp`s into constraints vs directives and emit this format.
-/

/-- Convert a `SpytialSpec` to a YAML string consumable by `parseLayoutSpec`. -/
public meta def SpytialSpec.toYaml (spec : SpytialSpec) : String :=
  let constraints := spec.filter SpytialOp.isConstraint
  let directives := spec.filter (! SpytialOp.isConstraint ·)
  let parts : List String := []
  let parts := if constraints.isEmpty then parts else
    parts ++ ["constraints:"] ++ constraints.map SpytialOp.toYamlLine
  let parts := if directives.isEmpty then parts else
    parts ++ ["directives:"] ++ directives.map SpytialOp.toYamlLine
  "\n".intercalate parts

/-- Extract constraint and directive lines from a YAML spec string.
    Returns `(constraintLines, directiveLines)`. -/
private meta def extractSpecLines (yaml : String) : List String × List String :=
  let lines := yaml.splitOn "\n"
  let rec go (lines : List String) (inConstraints : Bool)
      (cs : List String) (ds : List String) : List String × List String :=
    match lines with
    | [] => (cs.reverse, ds.reverse)
    | l :: rest =>
      if l == "constraints:" then go rest true cs ds
      else if l == "directives:" then go rest false cs ds
      else if l.startsWith "  - " then
        if inConstraints then go rest inConstraints (l :: cs) ds
        else go rest inConstraints cs (l :: ds)
      else go rest inConstraints cs ds
  go lines true [] []

/-- Merge multiple YAML spec strings (parent-first order) into a single YAML spec.
    Constraints and directives from all specs are concatenated in order. -/
public meta def mergeSpecYamls (yamls : List String) : String :=
  let (allCs, allDs) := yamls.foldl (fun (cs, ds) yaml =>
    let (c, d) := extractSpecLines yaml
    (cs ++ c, ds ++ d)) ([], [])
  let parts : List String := []
  let parts := if allCs.isEmpty then parts else parts ++ ["constraints:"] ++ allCs
  let parts := if allDs.isEmpty then parts else parts ++ ["directives:"] ++ allDs
  "\n".intercalate parts

end SpytialLean

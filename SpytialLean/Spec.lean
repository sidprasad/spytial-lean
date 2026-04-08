import Lean

namespace SpytialLean

/-- Relative positioning directions for orientation constraints. -/
inductive Direction where
  | above | below | left | right
  | directlyAbove | directlyBelow | directlyLeft | directlyRight
  deriving Repr, DecidableEq, Inhabited

/-- Alignment direction. -/
inductive AlignDir where
  | horizontal | vertical
  deriving Repr, DecidableEq, Inhabited

/-- Rotation direction for cyclic constraints. -/
inductive RotationDir where
  | clockwise | counterclockwise
  deriving Repr, DecidableEq, Inhabited

/-- Edge line style. -/
inductive EdgeStyle where
  | solid | dashed | dotted
  deriving Repr, DecidableEq, Inhabited

/-- A single Spytial operation — either a constraint (layout geometry) or a
    directive (visual styling). This matches the flat decorator lists used
    by spytial-py and caraspace (Rust). -/
inductive SpytialOp where
  -- Layout constraints
  | orientation (selector : String) (directions : List Direction)
  | align (selector : String) (direction : AlignDir)
  | cyclic (selector : String) (direction : RotationDir := .clockwise)
  | group (selector : String) (name : String) (addEdge : Bool := false)
  | hideAtom (selector : String)
  | size (selector : String) (width : Nat := 100) (height : Nat := 60)
  -- Visual directives
  | atomColor (selector : String) (value : String)
  | edgeColor (field : String) (value : String) (style : EdgeStyle := .solid)
  | hideField (field : String)
  | attribute (field : String)
  | icon (selector : String) (path : String) (showLabels : Bool := false)
  | tag (toTag : String) (name : String) (value : String)
  | inferredEdge (name : String) (selector : String)
      (color : String := "#000000") (style : EdgeStyle := .solid)
  | flag (name : String)
  deriving Repr, Inhabited

/-- A list of Spytial operations forming a complete layout specification. -/
abbrev SpytialSpec := List SpytialOp

/-! ## YAML serialization

`parseLayoutSpec` in spytial-core accepts YAML with two top-level keys:
```yaml
constraints:
  - orientation: { selector: "...", directions: [above, below] }
directives:
  - atomColor: { selector: "...", value: "#ff0000" }
```
We partition `SpytialOp`s into constraints vs directives and emit this format.
-/

private def Direction.toYaml : Direction → String
  | .above => "above"
  | .below => "below"
  | .left => "left"
  | .right => "right"
  | .directlyAbove => "directlyAbove"
  | .directlyBelow => "directlyBelow"
  | .directlyLeft => "directlyLeft"
  | .directlyRight => "directlyRight"

private def AlignDir.toYaml : AlignDir → String
  | .horizontal => "horizontal"
  | .vertical => "vertical"

private def RotationDir.toYaml : RotationDir → String
  | .clockwise => "clockwise"
  | .counterclockwise => "counterclockwise"

private def EdgeStyle.toYaml : EdgeStyle → String
  | .solid => "solid"
  | .dashed => "dashed"
  | .dotted => "dotted"

private def directionsToYaml (ds : List Direction) : String :=
  "[" ++ ", ".intercalate (ds.map Direction.toYaml) ++ "]"

/-- Is this op a constraint (affects layout geometry)? -/
private def SpytialOp.isConstraint : SpytialOp → Bool
  | .orientation .. | .align .. | .cyclic .. | .group .. => true
  | .hideAtom .. | .size .. => true
  | _ => false

/-- Render a single constraint op as a YAML list item. -/
private def constraintToYaml : SpytialOp → String
  | .orientation sel dirs =>
    s!"  - orientation: \{selector: \"{sel}\", directions: {directionsToYaml dirs}}"
  | .align sel dir =>
    s!"  - align: \{selector: \"{sel}\", direction: {dir.toYaml}}"
  | .cyclic sel dir =>
    s!"  - cyclic: \{selector: \"{sel}\", direction: {dir.toYaml}}"
  | .group sel name addEdge =>
    let ae := if addEdge then ", addEdge: true" else ""
    s!"  - group: \{selector: \"{sel}\", name: \"{name}\"{ae}}"
  | .hideAtom sel =>
    s!"  - hideAtom: \{selector: \"{sel}\"}"
  | .size sel w h =>
    s!"  - size: \{selector: \"{sel}\", width: {w}, height: {h}}"
  | _ => ""

/-- Render a single directive op as a YAML list item. -/
private def directiveToYaml : SpytialOp → String
  | .atomColor sel val =>
    s!"  - atomColor: \{selector: \"{sel}\", value: \"{val}\"}"
  | .edgeColor field val style =>
    s!"  - edgeColor: \{field: \"{field}\", value: \"{val}\", style: {style.toYaml}}"
  | .hideField field =>
    s!"  - hideField: \{field: \"{field}\"}"
  | .attribute field =>
    s!"  - attribute: \{field: \"{field}\"}"
  | .icon sel path showLabels =>
    let sl := if showLabels then ", showLabels: true" else ""
    s!"  - icon: \{selector: \"{sel}\", path: \"{path}\"{sl}}"
  | .tag toTag name value =>
    s!"  - tag: \{toTag: \"{toTag}\", name: \"{name}\", value: \"{value}\"}"
  | .inferredEdge name sel color style =>
    s!"  - inferredEdge: \{name: \"{name}\", selector: \"{sel}\", color: \"{color}\", style: {style.toYaml}}"
  | .flag name =>
    s!"  - flag: {name}"
  | .hideAtom sel =>
    s!"  - hideAtom: \{selector: \"{sel}\"}"
  | .size sel w h =>
    s!"  - size: \{selector: \"{sel}\", width: {w}, height: {h}}"
  | _ => ""

/-- Convert a `SpytialSpec` to a YAML string consumable by `parseLayoutSpec`. -/
def SpytialSpec.toYaml (spec : SpytialSpec) : String :=
  let constraints := spec.filter SpytialOp.isConstraint
  let directives := spec.filter (! SpytialOp.isConstraint ·)
  let parts : List String := []
  let parts := if constraints.isEmpty then parts else
    parts ++ ["constraints:"] ++ constraints.map constraintToYaml
  let parts := if directives.isEmpty then parts else
    parts ++ ["directives:"] ++ directives.map directiveToYaml
  "\n".intercalate parts

/-- Extract constraint and directive lines from a YAML spec string.
    Returns `(constraintLines, directiveLines)`. -/
private def extractSpecLines (yaml : String) : List String × List String :=
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
def mergeSpecYamls (yamls : List String) : String :=
  let (allCs, allDs) := yamls.foldl (fun (cs, ds) yaml =>
    let (c, d) := extractSpecLines yaml
    (cs ++ c, ds ++ d)) ([], [])
  let parts : List String := []
  let parts := if allCs.isEmpty then parts else parts ++ ["constraints:"] ++ allCs
  let parts := if allDs.isEmpty then parts else parts ++ ["directives:"] ++ allDs
  "\n".intercalate parts

end SpytialLean

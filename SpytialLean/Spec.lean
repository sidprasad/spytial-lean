module

public import Lean

namespace SpytialLean

/-- Relative positioning directions for orientation constraints. -/
public meta inductive Direction where
  | above | below | left | right
  | directlyAbove | directlyBelow | directlyLeft | directlyRight
  deriving Repr, DecidableEq, Inhabited

/-- Alignment direction. -/
public meta inductive AlignDir where
  | horizontal | vertical
  deriving Repr, DecidableEq, Inhabited

/-- Rotation direction for cyclic constraints. -/
public meta inductive RotationDir where
  | clockwise | counterclockwise
  deriving Repr, DecidableEq, Inhabited

/-- Edge line style. -/
public meta inductive EdgeStyle where
  | solid | dashed | dotted
  deriving Repr, DecidableEq, Inhabited

/-- A single Spytial operation — either a constraint (layout geometry) or a
    directive (visual styling). This matches the flat decorator lists used
    by spytial-py and caraspace (Rust). -/
public meta inductive SpytialOp where
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
public meta abbrev SpytialSpec := List SpytialOp

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

private meta def Direction.toYaml : Direction → String
  | .above => "above"
  | .below => "below"
  | .left => "left"
  | .right => "right"
  | .directlyAbove => "directlyAbove"
  | .directlyBelow => "directlyBelow"
  | .directlyLeft => "directlyLeft"
  | .directlyRight => "directlyRight"

private meta def AlignDir.toYaml : AlignDir → String
  | .horizontal => "horizontal"
  | .vertical => "vertical"

private meta def RotationDir.toYaml : RotationDir → String
  | .clockwise => "clockwise"
  | .counterclockwise => "counterclockwise"

private meta def EdgeStyle.toYaml : EdgeStyle → String
  | .solid => "solid"
  | .dashed => "dashed"
  | .dotted => "dotted"

private meta def directionsToYaml (ds : List Direction) : String :=
  "[" ++ ", ".intercalate (ds.map Direction.toYaml) ++ "]"

/-- A double-quoted YAML scalar. Escapes `\` and `"` — a selector carries `"`
    whenever it compares against a label literal (sgq 3.0 quoted strings). -/
private meta def yamlStr (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

/-- Is this op a constraint (affects layout geometry)? -/
private meta def SpytialOp.isConstraint : SpytialOp → Bool
  | .orientation .. | .align .. | .cyclic .. | .group .. => true
  | .hideAtom .. | .size .. => true
  | _ => false

/-- Render a single constraint op as a YAML list item. -/
private meta def constraintToYaml : SpytialOp → String
  | .orientation sel dirs =>
    s!"  - orientation: \{selector: {yamlStr sel}, directions: {directionsToYaml dirs}}"
  | .align sel dir =>
    s!"  - align: \{selector: {yamlStr sel}, direction: {dir.toYaml}}"
  | .cyclic sel dir =>
    s!"  - cyclic: \{selector: {yamlStr sel}, direction: {dir.toYaml}}"
  | .group sel name addEdge =>
    let ae := if addEdge then ", addEdge: true" else ""
    s!"  - group: \{selector: {yamlStr sel}, name: {yamlStr name}{ae}}"
  | .hideAtom sel =>
    s!"  - hideAtom: \{selector: {yamlStr sel}}"
  | .size sel w h =>
    s!"  - size: \{selector: {yamlStr sel}, width: {w}, height: {h}}"
  | _ => ""

/-- Render a single directive op as a YAML list item. -/
private meta def directiveToYaml : SpytialOp → String
  | .atomColor sel val =>
    s!"  - atomColor: \{selector: {yamlStr sel}, value: {yamlStr val}}"
  | .edgeColor field val style =>
    s!"  - edgeColor: \{field: {yamlStr field}, value: {yamlStr val}, style: {style.toYaml}}"
  | .hideField field =>
    s!"  - hideField: \{field: {yamlStr field}}"
  | .attribute field =>
    s!"  - attribute: \{field: {yamlStr field}}"
  | .icon sel path showLabels =>
    let sl := if showLabels then ", showLabels: true" else ""
    s!"  - icon: \{selector: {yamlStr sel}, path: {yamlStr path}{sl}}"
  | .tag toTag name value =>
    s!"  - tag: \{toTag: {yamlStr toTag}, name: {yamlStr name}, value: {yamlStr value}}"
  | .inferredEdge name sel color style =>
    s!"  - inferredEdge: \{name: {yamlStr name}, selector: {yamlStr sel}, color: {yamlStr color}, style: {style.toYaml}}"
  | .flag name =>
    s!"  - flag: {name}"
  | .hideAtom sel =>
    s!"  - hideAtom: \{selector: {yamlStr sel}}"
  | .size sel w h =>
    s!"  - size: \{selector: {yamlStr sel}, width: {w}, height: {h}}"
  | _ => ""

/-- Convert a `SpytialSpec` to a YAML string consumable by `parseLayoutSpec`. -/
public meta def SpytialSpec.toYaml (spec : SpytialSpec) : String :=
  let constraints := spec.filter SpytialOp.isConstraint
  let directives := spec.filter (! SpytialOp.isConstraint ·)
  let parts : List String := []
  let parts := if constraints.isEmpty then parts else
    parts ++ ["constraints:"] ++ constraints.map constraintToYaml
  let parts := if directives.isEmpty then parts else
    parts ++ ["directives:"] ++ directives.map directiveToYaml
  "\n".intercalate parts

end SpytialLean

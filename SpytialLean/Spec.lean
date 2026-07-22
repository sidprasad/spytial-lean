module

public import Lean
public meta import SpytialLean.Selector

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
    directive (visual styling). Selector positions carry checked `Sel` ASTs;
    `field` positions carry relation names validated against the target type's
    vocabulary at elaboration time. -/
public meta inductive SpytialOp where
  -- Layout constraints
  | orientation (selector : Sel) (directions : List Direction)
  | align (selector : Sel) (direction : AlignDir)
  | cyclic (selector : Sel) (direction : RotationDir := .clockwise)
  | group (selector : Sel) (name : String) (addEdge : Bool := false)
  | hideAtom (selector : Sel)
  | size (selector : Sel) (width : Nat := 100) (height : Nat := 60)
  -- Visual directives
  | atomColor (selector : Sel) (value : String)
  | edgeColor (field : String) (value : String) (style : EdgeStyle := .solid)
  | hideField (field : String)
  | attribute (field : String)
  | icon (selector : Sel) (path : String) (showLabels : Bool := false)
  | tag (toTag : Sel) (name : String) (value : String)
  | inferredEdge (name : String) (selector : Sel)
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
Selectors lower through `Sel.toSGQ` at emission time — the environment stores
the structured spec, and YAML exists only in the widget payload.
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

/-- Double-quote a string for YAML, escaping quotes and backslashes (selector
    strings can contain both, e.g. `@:x = "lit"`). -/
private meta def q (s : String) : String :=
  let escaped := s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | c => acc.push c
  s!"\"{escaped}\""

private meta def qSel (sel : Sel) : String := q sel.toSGQ

private meta def directionsToYaml (ds : List Direction) : String :=
  "[" ++ ", ".intercalate (ds.map Direction.toYaml) ++ "]"

/-- Is this op a constraint (affects layout geometry)? -/
private meta def SpytialOp.isConstraint : SpytialOp → Bool
  | .orientation .. | .align .. | .cyclic .. | .group .. => true
  | .hideAtom .. | .size .. => true
  | _ => false

/-- Render a single constraint op as a YAML list item. -/
private meta def constraintToYaml : SpytialOp → String
  | .orientation sel dirs =>
    s!"  - orientation: \{selector: {qSel sel}, directions: {directionsToYaml dirs}}"
  | .align sel dir =>
    s!"  - align: \{selector: {qSel sel}, direction: {dir.toYaml}}"
  | .cyclic sel dir =>
    s!"  - cyclic: \{selector: {qSel sel}, direction: {dir.toYaml}}"
  | .group sel name addEdge =>
    let ae := if addEdge then ", addEdge: true" else ""
    s!"  - group: \{selector: {qSel sel}, name: {q name}{ae}}"
  | .hideAtom sel =>
    s!"  - hideAtom: \{selector: {qSel sel}}"
  | .size sel w h =>
    s!"  - size: \{selector: {qSel sel}, width: {w}, height: {h}}"
  | _ => ""

/-- Render a single directive op as a YAML list item. -/
private meta def directiveToYaml : SpytialOp → String
  | .atomColor sel val =>
    s!"  - atomColor: \{selector: {qSel sel}, value: {q val}}"
  | .edgeColor field val style =>
    s!"  - edgeColor: \{field: {q field}, value: {q val}, style: {style.toYaml}}"
  | .hideField field =>
    s!"  - hideField: \{field: {q field}}"
  | .attribute field =>
    s!"  - attribute: \{field: {q field}}"
  | .icon sel path showLabels =>
    let sl := if showLabels then ", showLabels: true" else ""
    s!"  - icon: \{selector: {qSel sel}, path: {q path}{sl}}"
  | .tag toTag name value =>
    s!"  - tag: \{toTag: {qSel toTag}, name: {q name}, value: {q value}}"
  | .inferredEdge name sel color style =>
    s!"  - inferredEdge: \{name: {q name}, selector: {qSel sel}, color: {q color}, style: {style.toYaml}}"
  | .flag name =>
    s!"  - flag: {name}"
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

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

/-! ## Spec serialization

`parseLayoutSpec` in spytial-core is js-yaml's `yaml.load`, and JSON is valid
YAML, so we emit the spec as `Lean.Json`: structured (no hand-rolled string
quoting to get wrong), escape-safe, and stable in goldens. The shape has two
optional top-level keys:
```json
{"constraints": [{"orientation": {"selector": "…", "directions": ["above"]}}],
 "directives":  [{"atomStyle": {"selector": "…", "borderStyle": {"color": "#ff0000"}}}]}
```
`SpytialOp`s partition into constraints vs directives; each lowers to a single
`{opName: {…}}` object. Selectors lower through `Sel.toSGQ` here — the
environment stores the structured spec, and the wire string exists only in the
widget payload.
-/

open Lean (Json)

private meta def Direction.toStr : Direction → String
  | .above => "above"
  | .below => "below"
  | .left => "left"
  | .right => "right"
  | .directlyAbove => "directlyAbove"
  | .directlyBelow => "directlyBelow"
  | .directlyLeft => "directlyLeft"
  | .directlyRight => "directlyRight"

private meta def AlignDir.toStr : AlignDir → String
  | .horizontal => "horizontal"
  | .vertical => "vertical"

private meta def RotationDir.toStr : RotationDir → String
  | .clockwise => "clockwise"
  | .counterclockwise => "counterclockwise"

private meta def EdgeStyle.toStr : EdgeStyle → String
  | .solid => "solid"
  | .dashed => "dashed"
  | .dotted => "dotted"

/-- Is this op a constraint (affects layout geometry)? -/
private meta def SpytialOp.isConstraint : SpytialOp → Bool
  | .orientation .. | .align .. | .cyclic .. | .group .. => true
  | .hideAtom .. | .size .. => true
  | _ => false

/-- Lower one op to its `{opName: {…}}` JSON object, in spytial-core v3's style
    vocabulary. The AST keeps the legacy constructor names (`atomColor`, `edgeColor`),
    but the wire form is the non-deprecated `atomStyle`/`edgeStyle` with
    `borderStyle`/`lineStyle` blocks (a bare `atomColor`/`edgeColor` hits a
    console-warning desugar path, a v4 removal candidate); `inferredEdge` likewise
    carries its color/pattern in a `lineStyle` block rather than deprecated inline
    fields, and `group`'s edge flag lowers to the named direction `addEdge: "togroup"`.
    Optional fields (`addEdge`, `showLabels`) are emitted only when set. -/
private meta def SpytialOp.toJson (op : SpytialOp) : Json :=
  let sel (s : Sel) : Json := Json.str s.toSGQ
  match op with
  | .orientation s dirs =>
    Json.mkObj [("orientation", Json.mkObj
      [("selector", sel s),
       ("directions", Json.arr (dirs.map (fun d => Json.str d.toStr)).toArray)])]
  | .align s dir =>
    Json.mkObj [("align", Json.mkObj [("selector", sel s), ("direction", Json.str dir.toStr)])]
  | .cyclic s dir =>
    Json.mkObj [("cyclic", Json.mkObj [("selector", sel s), ("direction", Json.str dir.toStr)])]
  | .group s name addEdge =>
    Json.mkObj [("group", Json.mkObj <|
      [("selector", sel s), ("name", Json.str name)] ++
      (if addEdge then [("addEdge", Json.str "togroup")] else []))]
  | .hideAtom s =>
    Json.mkObj [("hideAtom", Json.mkObj [("selector", sel s)])]
  | .size s w h =>
    Json.mkObj [("size", Json.mkObj
      [("selector", sel s), ("width", Json.num (.fromNat w)), ("height", Json.num (.fromNat h))])]
  | .atomColor s val =>
    Json.mkObj [("atomStyle", Json.mkObj
      [("selector", sel s), ("borderStyle", Json.mkObj [("color", Json.str val)])])]
  | .edgeColor field val style =>
    Json.mkObj [("edgeStyle", Json.mkObj
      [("field", Json.str field),
       ("lineStyle", Json.mkObj [("color", Json.str val), ("pattern", Json.str style.toStr)])])]
  | .hideField field =>
    Json.mkObj [("hideField", Json.mkObj [("field", Json.str field)])]
  | .attribute field =>
    Json.mkObj [("attribute", Json.mkObj [("field", Json.str field)])]
  | .icon s path showLabels =>
    Json.mkObj [("icon", Json.mkObj <|
      [("selector", sel s), ("path", Json.str path)] ++
      (if showLabels then [("showLabels", Json.bool true)] else []))]
  | .tag toTag name value =>
    Json.mkObj [("tag", Json.mkObj
      [("toTag", sel toTag), ("name", Json.str name), ("value", Json.str value)])]
  | .inferredEdge name s color style =>
    Json.mkObj [("inferredEdge", Json.mkObj
      [("name", Json.str name), ("selector", sel s),
       ("lineStyle", Json.mkObj [("color", Json.str color), ("pattern", Json.str style.toStr)])])]
  | .flag name =>
    Json.mkObj [("flag", Json.str name)]

/-- Render a `SpytialSpec` as the spec string spytial-core consumes. Emitted as
    JSON, which is valid YAML for the core's js-yaml `parseLayoutSpec`; a spec
    with no ops renders as the empty string (not `{}`). -/
public meta def SpytialSpec.render (spec : SpytialSpec) : String :=
  let mkSection (key : String) (ops : SpytialSpec) : List (String × Json) :=
    if ops.isEmpty then [] else [(key, Json.arr (ops.map SpytialOp.toJson).toArray)]
  let (constraints, directives) := spec.partition SpytialOp.isConstraint
  match mkSection "constraints" constraints ++ mkSection "directives" directives with
  | [] => ""
  | kvs => (Json.mkObj kvs).pretty

end SpytialLean

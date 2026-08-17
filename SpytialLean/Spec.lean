module

public import Lean
public meta import SpytialLean.Selector

namespace SpytialLean

open Lean (Json ToJson FromJson toJson)

/-- Relative positioning directions for orientation constraints. -/
public meta inductive Direction where
  | above | below | left | right
  | directlyAbove | directlyBelow | directlyLeft | directlyRight
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- Alignment direction. -/
public meta inductive AlignDir where
  | horizontal | vertical
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- Rotation direction for cyclic constraints. -/
public meta inductive RotationDir where
  | clockwise | counterclockwise
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- Edge line style. -/
public meta inductive EdgeStyle where
  | solid | dashed | dotted
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

public meta instance : ToJson Sel := ⟨fun s => Json.str s.toSGQ⟩

/-- Selector positions carry checked `Sel`s; `field` positions carry relation
    names validated against the target type's vocabulary. -/
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
YAML, so we emit the spec as `Lean.Json`, escape-safe.
The shape has two optional top-level keys:
```json
{"constraints": [{"orientation": {"selector": "…", "directions": ["above"]}}],
 "directives":  [{"atomColor": {"selector": "…", "value": "#ff0000"}}]}
```
`SpytialOp`s partition into constraints vs directives; each lowers to a single
`{opName: …}` object. Selectors lower through `Sel.toSGQ` here — the
environment stores the structured spec, and the wire string exists only in the
widget payload.
-/

/-- Is this op a constraint (affects layout geometry)? -/
private meta def SpytialOp.isConstraint : SpytialOp → Bool
  | .orientation .. | .align .. | .cyclic .. | .group .. => true
  | .hideAtom .. | .size .. => true
  | _ => false

deriving instance ToJson for SpytialOp

public meta instance : ToJson SpytialOp where
  toJson
    -- core matches flags by string, so the payload is the bare name
    | .flag name => Json.mkObj [("flag", toJson name)]
    | op => instToJsonSpytialOp.toJson op

/-- A spec with no ops renders as the empty string, not `{}`. -/
public meta def SpytialSpec.render (spec : SpytialSpec) : String :=
  let mkSection (key : String) (ops : SpytialSpec) : List (String × Json) :=
    if ops.isEmpty then [] else [(key, toJson ops)]
  let (constraints, directives) := spec.partition SpytialOp.isConstraint
  match mkSection "constraints" constraints ++ mkSection "directives" directives with
  | [] => ""
  | kvs => (Json.mkObj kvs).pretty

end SpytialLean

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

/-- Line pattern, for `lineStyle` blocks. -/
public meta inductive LinePattern where
  | solid | dashed | dotted
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-- Icon placement: `full` occupies the atom's box, `badge` is a top-right
    marker secondary to the label. -/
public meta inductive IconPlacement where
  | full | badge
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

public meta inductive GroupEdgeDirection where
  | togroup | fromgroup
  deriving Repr, DecidableEq, Inhabited, ToJson, FromJson

/-! ## Style blocks

Sparse structs mirroring core's style blocks; only set fields reach the wire.
The op elaborator fills them from `(blockName arg…)` surface blocks. -/

public meta structure BorderStyle where
  color : Option String := none
  width : Option Nat := none
  deriving Repr, Inhabited

public meta structure FillStyle where
  color : Option String := none
  deriving Repr, Inhabited

public meta structure IconStyle where
  path : String
  placement : Option IconPlacement := none
  deriving Repr, Inhabited

public meta structure LineStyle where
  color : Option String := none
  pattern : Option LinePattern := none
  weight : Option Nat := none
  deriving Repr, Inhabited

public meta structure GroupEdge where
  direction : GroupEdgeDirection
  lineStyle : Option LineStyle := none
  deriving Repr, Inhabited

public meta instance : ToJson Sel := ⟨fun s => Json.str s.toSGQ⟩

/-- Selector positions carry checked `Sel`s; `field` positions carry relation
    names validated against the target type's vocabulary. Style ops carry the
    sparse blocks; an op with nothing set is rejected at elaboration. -/
public meta inductive SpytialOp where
  -- Layout constraints
  | orientation (selector : Sel) (directions : List Direction)
  | align (selector : Sel) (direction : AlignDir)
  | cyclic (selector : Sel) (direction : RotationDir := .clockwise)
  | group (selector : Sel) (name : String) (addEdge : Option GroupEdge := none)
  | hideAtom (selector : Sel)
  | size (selector : Sel) (width : Nat := 100) (height : Nat := 60)
  -- Visual directives
  | atomStyle (selector : Sel) (border : Option BorderStyle := none)
      (fill : Option FillStyle := none) (icon : Option IconStyle := none)
      (showLabel : Option Bool := none)
  | edgeStyle (field : String) (line : Option LineStyle := none)
      (showLabel : Option Bool := none)
  | hideField (field : String)
  | attribute (field : String)
  | tag (toTag : Sel) (name : String) (value : String)
  | inferredEdge (name : String) (selector : Sel) (line : Option LineStyle := none)
  | flag (name : String)
  deriving Repr, Inhabited

/-- Where an op was written. Spytial is a *generator* of specs, so the wire
    form carries the Lean the user actually wrote: core cites this in conflict
    reports and warnings in place of its own rendering of the rule, which for a
    resolved Lean selector would otherwise be a list of atom ids. -/
public meta structure OpSource where
  /-- The op exactly as written, e.g. `hideAtom lean (RBNode.isLeaf)`. -/
  text : String
  /-- `File.lean:12`, appended to the displayed text. -/
  location : Option String := none
  deriving Repr, Inhabited

/-- Stamp each layout constraint with the Lean it was written as. On by
    default: it is what makes a conflict report cite the user's own line
    instead of the engine's rendering. Turn it off to keep the emitted spec
    free of source text — the goldens that pin lowering do, rather than
    restate a stamp on every op. -/
public meta register_option spytial.source : Bool := {
  defValue := true
  descr := "carry each layout constraint's own source text in the emitted \
            spec, for conflict reports"
}

/-- An op together with the source it was written as. Attached specs store the
    stamp, so a spec re-run in another file still cites where it was declared. -/
public meta structure StampedOp where
  op : SpytialOp
  source : Option OpSource := none
  deriving Repr, Inhabited

/-- A list of Spytial operations forming a complete layout specification. -/
public meta abbrev SpytialSpec := List StampedOp

/-- The graph-side name an op introduces, with its arity. -/
public meta def SpytialOp.introduces? : SpytialOp → Option (String × Nat)
  | .group _ name _ => some (name, 1)
  | .inferredEdge name _ _ => some (name, 2)
  | _ => none

/-! ## Spec serialization

`parseLayoutSpec` in spytial-core is js-yaml's `yaml.load`, and JSON is valid
YAML, so we emit the spec as `Lean.Json`, escape-safe.
The shape has two optional top-level keys:
```json
{"constraints": [{"orientation": {"selector": "…", "directions": ["above"]}}],
 "directives":  [{"atomStyle": {"selector": "…", "borderStyle": {"color": "#ff0000"}}}]}
```
`SpytialOp`s partition into constraints vs directives; each lowers to a single
`{opName: …}` object. Selectors lower through `Sel.toSGQ` here — the
environment stores the structured spec, and the wire string exists only in the
widget payload.
-/

/-- Is this op a constraint (affects layout geometry)? Also decides which ops
    carry their `source` on the wire: core cites the constraints. -/
public meta def SpytialOp.isConstraint : SpytialOp → Bool
  | .orientation .. | .align .. | .cyclic .. | .group .. => true
  | .hideAtom .. | .size .. => true
  | _ => false

/-- An object from the fields that are set; `none`s are omitted, never
    `null` (core treats an absent key and an explicit `null` differently). -/
public meta def objOpt (kvs : List (String × Option Json)) : Json :=
  Json.mkObj <| kvs.filterMap fun (k, v?) => v?.map ((k, ·))

public meta instance : ToJson BorderStyle := ⟨fun b => objOpt
  [("color", b.color.map toJson), ("width", b.width.map toJson)]⟩
public meta instance : ToJson FillStyle := ⟨fun f => objOpt
  [("color", f.color.map toJson)]⟩
public meta instance : ToJson IconStyle := ⟨fun i => objOpt
  [("path", some (toJson i.path)), ("placement", i.placement.map toJson)]⟩
public meta instance : ToJson LineStyle := ⟨fun l => objOpt
  [("color", l.color.map toJson), ("pattern", l.pattern.map toJson),
   ("weight", l.weight.map toJson)]⟩

/-- A direction-only edge is the bare string form; with styling it is the
    block form, whose direction key is `points`. -/
public meta instance : ToJson GroupEdge := ⟨fun g =>
  match g.lineStyle with
  | none => toJson g.direction
  | some ls => Json.mkObj [("points", toJson g.direction), ("lineStyle", toJson ls)]⟩

deriving instance ToJson for SpytialOp

/-- The style ops emit sparse objects (`objOpt`); the rest keep the derived
    shape. `flag`'s payload is the bare name — core matches flags by string. -/
public meta instance : ToJson SpytialOp where
  toJson
    | .atomStyle s border fill icon showLabel =>
      Json.mkObj [("atomStyle", objOpt
        [("selector", some (toJson s)), ("borderStyle", border.map toJson),
         ("fillStyle", fill.map toJson), ("iconStyle", icon.map toJson),
         ("showLabel", showLabel.map toJson)])]
    | .edgeStyle field line showLabel =>
      Json.mkObj [("edgeStyle", objOpt
        [("field", some (toJson field)), ("lineStyle", line.map toJson),
         ("showLabel", showLabel.map toJson)])]
    | .inferredEdge name s line =>
      Json.mkObj [("inferredEdge", objOpt
        [("name", some (toJson name)), ("selector", some (toJson s)),
         ("lineStyle", line.map toJson)])]
    | .group s name addEdge =>
      Json.mkObj [("group", objOpt
        [("selector", some (toJson s)), ("name", some (toJson name)),
         ("addEdge", addEdge.map toJson)])]
    | .flag name => Json.mkObj [("flag", toJson name)]
    | op => instToJsonSpytialOp.toJson op

public meta instance : ToJson OpSource := ⟨fun s => objOpt
  [("text", some (toJson s.text)), ("location", s.location.map toJson)]⟩

/-- An op renders as `{opName: body}`, and core reads `source` from inside
    `body`. Only the constraints carry it: those are the ops core cites in
    conflict reports, and on a directive it would be payload core parses and
    ignores. `flag`'s payload is the bare name, with nowhere to put it. -/
public meta instance : ToJson StampedOp where
  toJson s :=
    let j := toJson s.op
    match s.source with
    | some src =>
      if s.op.isConstraint then
        match j.getObj? with
        | .ok kvs =>
          match kvs.toList with
          | [(key, body@(.obj _))] =>
            Json.mkObj [(key, body.setObjVal! "source" (toJson src))]
          | _ => j
        | _ => j
      else j
    | none => j

/-- A spec with no ops renders as the empty string, not `{}`. -/
public meta def SpytialSpec.render (spec : SpytialSpec) : String :=
  let mkSection (key : String) (ops : SpytialSpec) : List (String × Json) :=
    if ops.isEmpty then [] else [(key, toJson ops)]
  let (constraints, directives) := spec.partition (SpytialOp.isConstraint ·.op)
  match mkSection "constraints" constraints ++ mkSection "directives" directives with
  | [] => ""
  | kvs => (Json.mkObj kvs).pretty

end SpytialLean

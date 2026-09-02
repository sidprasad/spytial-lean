module

public import Lean
public meta import SpytialLean.Selector
public meta import SpytialLean.SpecLang

namespace SpytialLean

open Lean (Json ToJson toJson JsonNumber DeclarationLocation)
open SpecLang

/-! ## The op AST -/

/-- Which constructor a field carries is a function of its `FieldType`; the
    elaborator establishes it and the lowering relies on it. -/
public meta inductive FieldVal where
  | sel (s : Sel)
  | rel (name : String)
  | str (s : String)
  | «enum» (value : String)
  | enums (values : List String)
  | num (n : JsonNumber)
  | bool (b : Bool)
  /-- The set fields of the field's `BlockSpec`, or — on an enum field with an
      `AltForm` — of the block alternative. -/
  | block (fields : List (FieldId × FieldVal))
  deriving Repr, Inhabited

/-- The Lean an op was written as, which core cites in conflict reports and
    warnings in place of its own rendering of the rule. -/
public meta structure OpSource where
  text : String
  /-- `File.lean:12`, appended to the displayed text. -/
  location : Option String := none
  deriving Repr, Inhabited

public meta register_option spytial.source : Bool := {
  defValue := true
  descr := "carry each layout constraint's own source text in the emitted \
            spec, for conflict reports"
}

/-- Unset optional fields are absent, not defaulted: the serialized spec
    carries what the source said and core supplies its own defaults. -/
public meta structure SpytialOp where
  item : ItemId
  fields : List (FieldId × FieldVal)
  /-- `hold: never`; only `ItemSpec.supportsHold` items carry it. -/
  hold : Option String := none
  source : Option OpSource := none
  /-- Where an introducing op wrote its graph-side name. Rides the op through
      bundles and attached specs so references elsewhere can jump to it; never
      serialized. -/
  nameDecl : Option DeclarationLocation := none
  deriving Repr, Inhabited

public meta abbrev SpytialSpec := List SpytialOp

public meta def SpytialOp.field? (op : SpytialOp) (f : FieldId) : Option FieldVal :=
  op.fields.lookup f

public meta def SpytialOp.introduces? (op : SpytialOp) : Option (String × Introduces) := do
  let i ← (ItemSpec.of op.item).introduces
  match op.field? i.field with
  | some (.str s) => some (s, i)
  | _ => none

/-! ## Checking an op against the tables

The elaborator builds ops that fit their item. Anything else that builds one
meets the same check here, at the boundary every spec crosses. -/

private meta def FieldVal.fits : FieldVal → FieldType → Bool
  | .sel _, .selector _ | .rel _, .relation
  | .str _, .str | .str _, .iconPath | .str _, .color
  | .num _, .number .. | .bool _, .boolean _ => true
  | .«enum» v, .«enum» vs _ => vs.contains v
  | .enums vs, .enumList all _ => vs.all all.contains
  | _, _ => false

mutual

private meta partial def FieldVal.check (path : String) (f : FieldSpec) :
    FieldVal → Except String Unit
  | .block fs =>
    match f.type, f.alt with
    | .block bid, _ => checkFields path (BlockSpec.of bid).fields [] fs
    | .«enum» vs _, some alt =>
      let specs := alt.blocks.map (fun (bf, bid) =>
          ({ id := bf, type := .block bid, required := false, alt := none } : FieldSpec))
        ++ [{ id := alt.enumField, type := .«enum» vs none, required := true, alt := none }]
      checkFields path specs [alt.enumField] fs
    | _, _ => .error s!"{path} is not a block field"
  | v => unless v.fits f.type do .error s!"{path} holds a value of the wrong shape"

private meta partial def checkFields (path : String) (specs : List FieldSpec)
    (required : List FieldId) (fs : List (FieldId × FieldVal)) : Except String Unit := do
  for (fid, v) in fs do
    let some f := specs.find? (·.id == fid)
      | .error s!"{path} has no field {fieldName fid}"
    if 1 < (fs.filter (·.1 == fid)).length then
      .error s!"{path}.{fieldName fid} is set twice"
    v.check s!"{path}.{fieldName fid}" f
  for r in required do
    unless fs.any (·.1 == r) do .error s!"{path} is missing {fieldName r}"

end

public meta def SpytialOp.check (op : SpytialOp) : Except String Unit := do
  let i := ItemSpec.of op.item
  let path := itemName op.item
  checkFields path i.fields ((i.fields.filter (·.required)).map (·.id)) op.fields
  if let some h := op.hold then
    unless i.supportsHold do .error s!"{path} does not support hold"
    unless holdValues.contains h do .error s!"{path}: hold must be one of {holdValues}"

/-! ## Spec serialization

`parseLayoutSpec` in spytial-core is js-yaml's `yaml.load` and JSON is valid
YAML, so the spec is emitted as `Lean.Json`, escape-safe. -/

public meta partial def FieldVal.toJson : FieldVal → Except String Json
  | .sel s => Json.str <$> s.toSGQ
  | .rel s | .str s | .«enum» s => .ok (Json.str s)
  | .enums vs => .ok (Lean.toJson vs)
  | .num n => .ok (Json.num n)
  | .bool b => .ok (Json.bool b)
  | .block fs => do
    return Json.mkObj (← fs.mapM fun (f, v) => do return (fieldName f, ← v.toJson))

public meta instance : ToJson OpSource where
  toJson s := Json.mkObj <|
    (fieldName .text, Json.str s.text) ::
      (s.location.map fun l => (fieldName .location, Json.str l)).toList

public meta def SpytialOp.toJson (op : SpytialOp) : Except String Json := do
  op.check
  let i := ItemSpec.of op.item
  let fields ← op.fields.mapM fun (f, v) => do return (fieldName f, ← v.toJson)
  -- A scalar payload has nowhere to put these.
  let extras :=
    (op.hold.map fun h => (holdField, Json.str h)).toList ++
    (if i.displaysSource then (op.source.map (sourceField, Lean.toJson ·)).toList else [])
  let payload ← match i.scalar, op.fields with
    | true, [(_, v)] => v.toJson
    | _, _ => .ok (Json.mkObj (fields ++ extras))
  return Json.mkObj [(i.yamlKey, payload)]

/-- A spec with no ops renders as the empty string, not `{}`. -/
public meta def SpytialSpec.render (spec : SpytialSpec) : Except String String := do
  let mkSection (key : String) (ops : SpytialSpec) : Except String (List (String × Json)) := do
    if ops.isEmpty then return []
    return [(key, Json.arr (← ops.toArray.mapM SpytialOp.toJson))]
  let (constraints, directives) :=
    spec.partition fun op => (ItemSpec.of op.item).constraint
  match (← mkSection "constraints" constraints) ++ (← mkSection "directives" directives) with
  | [] => return ""
  | kvs => return (Json.mkObj kvs).pretty

end SpytialLean

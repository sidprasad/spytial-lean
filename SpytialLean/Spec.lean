module

public import Lean
public meta import SpytialLean.Selector
public meta import SpytialLean.SpecLang

namespace SpytialLean

open Lean (Json ToJson toJson JsonNumber)
open SpecLang

/-! ## The op AST

One node type: a manifest item plus the fields that were set, each parsed to
the shape its `FieldType` declares. Nothing here names an item, so an item or
field added upstream needs no new constructor — the same ruling as the
selector AST, where a generated typed inductive would buy exhaustiveness only
for consumers that do not exist and every `match` over it would be an edit. -/

/-- A field's elaborated value. Which constructor a field carries is a
    function of its `FieldType`; the elaborator establishes it and the
    lowering relies on it. -/
public meta inductive FieldVal where
  /-- A checked selector (`selector`, `filter`, `toTag`, `value`). -/
  | sel (s : Sel)
  /-- A relation name from the walker's vocabulary (`field`). -/
  | rel (name : String)
  | str (s : String)
  /-- A validated member of the field's enum. -/
  | «enum» (value : String)
  /-- A validated enum-list (`orientation.directions`). -/
  | enums (values : List String)
  | num (n : JsonNumber)
  | bool (b : Bool)
  /-- A block instance: the set fields of its `BlockSpec` — or, on an enum
      field with an `AltForm`, the block alternative (`group.addEdge`'s
      `{points, lineStyle, textStyle}`). -/
  | block (fields : List (FieldId × FieldVal))
  deriving Repr, Inhabited

/-- One Spytial operation: a manifest item with its set fields. Unset
    optional fields are absent, not defaulted — the wire carries what the
    source said and core supplies its own defaults. -/
public meta structure SpytialOp where
  item : ItemId
  fields : List (FieldId × FieldVal)
  /-- `hold: never` negates a constraint; only items with
      `ItemSpec.supportsHold` carry it. -/
  hold : Option String := none
  deriving Repr, Inhabited

/-- A list of Spytial operations forming a complete layout specification. -/
public meta abbrev SpytialSpec := List SpytialOp

public meta def SpytialOp.field? (op : SpytialOp) (f : FieldId) : Option FieldVal :=
  op.fields.lookup f

/-- The graph-side name an op introduces, with its arity. Which field is the
    handle is the table's `introduces` — manifest prose the generator pins. -/
public meta def SpytialOp.introduces? (op : SpytialOp) : Option (String × Nat) := do
  let (f, arity) ← (ItemSpec.of op.item).introduces
  match op.field? f with
  | some (.str s) => some (s, arity)
  | _ => none

/-! ## Spec serialization

`parseLayoutSpec` in spytial-core is js-yaml's `yaml.load`, and JSON is valid
YAML, so we emit the spec as `Lean.Json`, escape-safe.
The shape has two optional top-level keys:
```json
{"constraints": [{"orientation": {"selector": "…", "directions": ["above"]}}],
 "directives":  [{"atomStyle": {"selector": "…", "borderStyle": {"color": "#ff0000"}}}]}
```
Which section an item lowers into is the table's `constraint`; each op lowers
to a single `{yamlKey: …}` object over its set fields (a `scalar` item's one
field is the payload itself). Selectors lower through `Sel.toSGQ` here — the
environment stores the structured spec, and the wire string exists only in
the widget payload.
-/

public meta instance : ToJson Sel := ⟨fun s => Json.str s.toSGQ⟩

public meta partial def FieldVal.toJson : FieldVal → Json
  | .sel s => Lean.toJson s
  | .rel s | .str s | .«enum» s => Json.str s
  | .enums vs => Lean.toJson vs
  | .num n => Json.num n
  | .bool b => Json.bool b
  | .block fs => Json.mkObj (fs.map fun (f, v) => (fieldName f, v.toJson))

public meta instance : ToJson SpytialOp where
  toJson op :=
    let i := ItemSpec.of op.item
    let fields := op.fields.map fun (f, v) => (fieldName f, v.toJson)
    let payload :=
      match i.scalar, op.fields with
      | true, [(_, v)] => v.toJson
      | _, _ => Json.mkObj <| fields ++
          (op.hold.map fun h => (holdField, Json.str h)).toList
    Json.mkObj [(i.yamlKey, payload)]

/-- A spec with no ops renders as the empty string, not `{}`. -/
public meta def SpytialSpec.render (spec : SpytialSpec) : String :=
  let mkSection (key : String) (ops : SpytialSpec) : List (String × Json) :=
    if ops.isEmpty then [] else [(key, toJson ops)]
  let (constraints, directives) :=
    spec.partition fun op => (ItemSpec.of op.item).constraint
  match mkSection "constraints" constraints ++ mkSection "directives" directives with
  | [] => ""
  | kvs => (Json.mkObj kvs).pretty

end SpytialLean

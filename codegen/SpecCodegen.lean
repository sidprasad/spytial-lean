/-
Generates `SpytialLean/SpecGenerated.lean` from spytial-core's language manifest.

    lake exe specCodegen           # regenerate (also: just gen-spec)
    lake exe specCodegen --check   # fail if the checked-in file is stale (CI)

spytial-core publishes `docs/spytial-language.json`, a machine-readable
description of every constraint and directive its layout-spec parser reads:
which section each belongs in, which fields it takes, which of those are
required, what each enum accepts, numeric bounds, and which forms are
deprecated. The npm package ships it, so the copy under
`widget/node_modules/spytial-core/docs/` is pinned by the workspace
`pnpm-lock.yaml` to the *same release as the embedded renderer* — the
authoring surface and the renderer cannot drift apart.

This program turns that manifest into the `SpytialOp` inductive, its enum and
style-block types, the YAML serialization, and validation/deprecation tables.
They used to be maintained by hand against spytial-core 2.x, so a core release
could add a field or deprecate a form and the Lean side would go on accepting
exactly what it accepted before, with nothing anywhere to say otherwise —
and core's parser silently ignores what it does not recognize.

The generator refuses to emit output it cannot account for. Every item, field
type, enum, block, and deprecation kind in the manifest has to map onto
something below; one that does not is an error naming the construct, so a
spytial-core bump that grows the language stops codegen by name rather than
dropping the feature.

Where the Lean surface deliberately differs from the manifest, the difference
lives in an override table below with the reason it exists. Everything else is
mechanical.
-/
import Lean.Data.Json

open Lean (Json JsonNumber)

def manifestPath : System.FilePath :=
  "widget" / "node_modules" / "spytial-core" / "docs" / "spytial-language.json"

def outputPath : System.FilePath := "SpytialLean" / "SpecGenerated.lean"

def die {α} (msg : String) : IO α := throw (IO.userError s!"spec-codegen: {msg}")

def unwrap {α} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => die s!"{ctx}: {e}"

/-! ## JSON access helpers -/

def jObj (ctx : String) (j : Json) (k : String) : IO Json :=
  unwrap s!"{ctx}.{k}" (j.getObjVal? k)

def jStr (ctx : String) (j : Json) (k : String) : IO String := do
  unwrap s!"{ctx}.{k}" (← jObj ctx j k).getStr?

def jArr (ctx : String) (j : Json) (k : String) : IO (Array Json) := do
  unwrap s!"{ctx}.{k}" (← jObj ctx j k).getArr?

def jStrArr (ctx : String) (j : Json) (k : String) : IO (Array String) := do
  (← jArr ctx j k).mapM fun v => unwrap s!"{ctx}.{k}[]" v.getStr?

def jOpt (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok v => if v.isNull then none else some v
  | .error _ => none

def jOptStr (ctx : String) (j : Json) (k : String) : IO (Option String) :=
  match jOpt j k with
  | some v => some <$> unwrap s!"{ctx}.{k}" v.getStr?
  | none => pure none

def jOptBool (ctx : String) (j : Json) (k : String) : IO (Option Bool) :=
  match jOpt j k with
  | some v => some <$> unwrap s!"{ctx}.{k}" v.getBool?
  | none => pure none

def jOptNum (ctx : String) (j : Json) (k : String) : IO (Option JsonNumber) :=
  match jOpt j k with
  | some v => some <$> unwrap s!"{ctx}.{k}" v.getNum?
  | none => pure none

def objKeys (j : Json) : List String :=
  match j with
  | .obj kvs => kvs.toArray.toList.map (·.1)
  | _ => []

/-! ## Overrides: where the Lean surface deliberately differs from the manifest -/

/-- Manifest item id → `SpytialOp` constructor name. Every item must appear
    here; a new upstream form fails codegen by name instead of being dropped.
    `group.byField` is spelled `groupByField` because `.` cannot appear in a
    constructor name. -/
def ctorName : String → Option String
  | "orientation"   => some "orientation"
  | "cyclic"        => some "cyclic"
  | "align"         => some "align"
  | "group"         => some "group"
  | "group.byField" => some "groupByField"
  | "size"          => some "size"
  | "hideAtom"      => some "hideAtom"
  | "flag"          => some "flag"
  | "atomStyle"     => some "atomStyle"
  | "edgeStyle"     => some "edgeStyle"
  | "attribute"     => some "attribute"
  | "tag"           => some "tag"
  | "hideField"     => some "hideField"
  | "inferredEdge"  => some "inferredEdge"
  | "icon"          => some "icon"
  | "atomColor"     => some "atomColor"
  | "edgeColor"     => some "edgeColor"
  | _ => none

/-- (owner, field) → Lean enum type name, where owner is an item id or
    `block:<name>`. Every enum in the manifest must appear here — that is how
    a newly added vocabulary announces itself instead of going unvalidated.
    `Direction`/`RotationDir`/`AlignDir` keep the names the hand-written 2.x
    surface used, so existing call sites keep compiling. -/
def enumTypeName : String → String → Option String
  | "orientation", "directions"   => some "Direction"
  | "cyclic", "direction"         => some "RotationDir"
  | "align", "direction"          => some "AlignDir"
  | "flag", "flag"                => some "FlagName"
  | "group", "addEdge"            => some "GroupEdge"
  | "inferredEdge", "style"       => some "LinePattern"
  | "edgeColor", "style"          => some "LinePattern"
  | "block:textStyle", "size"     => some "TextSize"
  | "block:lineStyle", "pattern"  => some "LinePattern"
  | "block:iconStyle", "placement" => some "IconPlacement"
  | _, _ => none

/-- Manifest enum value → Lean constructor name. The YAML spelling is whatever
    the manifest says; only the Lean-side ident differs, for readability. -/
def valueCtor : String → String
  | "togroup"   => "toGroup"
  | "fromgroup" => "fromGroup"
  | v => v

/-- (item, field) → Lean parameter name, where the two differ.
    `flag` is a scalar item: the YAML is `- flag: hideDisconnected`, so the
    manifest names the field after the item. As a Lean parameter that would
    read `.flag (flag := ...)`, so the constructor takes `name`. -/
def paramName (item field : String) : String :=
  match item, field with
  | "flag", "flag" => "name"
  | _, _ => field

/-- (item, field) pairs whose manifest type `number` is narrowed to `Nat`.
    Node dimensions are pixel counts; `Nat` literals are the natural authoring
    surface and every `Nat` is a valid manifest number. -/
def natNumberFields : List (String × String) := [("size", "width"), ("size", "height")]

/-! ## Manifest model -/

structure BoundCheck where
  /-- Lean comparison producing `True` when the value is OUT of bounds,
      with `v` free, e.g. `v <= 0`. -/
  cond : String
  /-- human message suffix, e.g. `must be > 0` -/
  msg : String
  deriving Inhabited

structure FieldInfo where
  yaml : String
  param : String
  ftype : String
  required : Bool
  values : Array String := #[]
  enumType : String := ""
  blockType : String := ""
  defaultStr : Option String := none
  bounds : List BoundCheck := []
  deprecatedFor : Option String := none
  listRules : Option Json := none
  description : Option String := none
  deriving Inhabited

structure ItemInfo where
  id : String
  yamlKey : String
  ctor : String
  isConstraint : Bool
  scalar : Bool
  supportsHold : Bool
  fields : Array FieldInfo
  description : Option String := none
  /-- deprecation message when the whole form is deprecated -/
  deprecatedMsg : Option String := none
  deriving Inhabited

/-! ## Parsing -/

def parseBounds (ctx : String) (j : Json) : IO (List BoundCheck) := do
  let mut out := []
  if let some n ← jOptNum ctx j "exclusiveMinimum" then
    out := out ++ [⟨s!"v <= {n}", s!"must be > {n}"⟩]
  if let some n ← jOptNum ctx j "minimum" then
    out := out ++ [⟨s!"v < {n}", s!"must be >= {n}"⟩]
  if let some n ← jOptNum ctx j "exclusiveMaximum" then
    out := out ++ [⟨s!"v >= {n}", s!"must be < {n}"⟩]
  if let some n ← jOptNum ctx j "maximum" then
    out := out ++ [⟨s!"v > {n}", s!"must be <= {n}"⟩]
  return out

/-- `owner` is the item id or `block:<name>`, for enum-name resolution. -/
def parseField (owner : String) (itemForParam : String) (j : Json) : IO FieldInfo := do
  let name ← jStr owner j "name"
  let ctx := s!"{owner}.{name}"
  let ftype ← jStr ctx j "type"
  let required := (← jOptBool ctx j "required").getD false
  let mut fi : FieldInfo := {
    yaml := name
    param := paramName itemForParam name
    ftype
    required
    bounds := ← parseBounds ctx j
    listRules := jOpt j "listRules"
    description := ← jOptStr ctx j "description"
  }
  match ftype with
  | "enum" | "enum-list" =>
    let some ty := enumTypeName owner name
      | die s!"{ctx}: enum vocabulary has no Lean type name in `enumTypeName` — add one"
    fi := { fi with values := ← jStrArr ctx j "values", enumType := ty }
    if let some d ← jOptStr ctx j "default" then
      fi := { fi with defaultStr := some d }
  | "block" =>
    fi := { fi with blockType := name.capitalize }
  | "selector" | "relation" | "string" | "color" | "icon-path" | "number" | "integer" | "boolean" =>
    pure ()
  | other => die s!"{ctx}: field type `{other}` is not something this generator was written for"
  if let some dep := jOpt j "deprecated" then
    fi := { fi with deprecatedFor := some (← jStr s!"{ctx}.deprecated" dep "replacedBy") }
  return fi

/-! ## Emission helpers -/

/-- Keep manifest prose safe inside a Lean doc comment. -/
def sanitizeDoc (s : String) : String :=
  ((s.replace "-/" "- /").replace "/-" "/ -").replace "\n" " "

def docComment (indent : String) : Option String → Array String
  | some d => #[s!"{indent}/-- {sanitizeDoc d} -/"]
  | none => #[]

/-- The Lean signature for one field, e.g. `selector : String` — unwrapped, so
    it serves both as a structure field line and (parenthesized) as a
    constructor binder. -/
def paramSig (it : ItemInfo) (f : FieldInfo) : IO String := do
  let p := f.param
  match f.ftype with
  | "selector" | "relation" | "string" | "color" | "icon-path" =>
    return if f.required then s!"{p} : String" else s!"{p} : Option String := none"
  | "enum" =>
    if f.required then return s!"{p} : {f.enumType}"
    -- Block fields stay `Option` even when the manifest names a default: a
    -- block is omitted from the YAML only when every field is unset, so a
    -- baked default would make the block impossible to leave out.
    else if it.id.startsWith "block:" then return s!"{p} : Option {f.enumType} := none"
    else match f.defaultStr with
      | some d => return s!"{p} : {f.enumType} := .{valueCtor d}"
      | none => return s!"{p} : Option {f.enumType} := none"
  | "enum-list" =>
    unless f.required do die s!"{it.id}.{f.yaml}: optional enum-list is unhandled"
    return s!"{p} : List {f.enumType}"
  | "boolean" =>
    unless !f.required do die s!"{it.id}.{f.yaml}: required boolean is unhandled"
    return s!"{p} : Option Bool := none"
  | "number" =>
    if natNumberFields.contains (it.id, f.yaml) then
      unless f.required do die s!"{it.id}.{f.yaml}: optional Nat-narrowed number is unhandled"
      return s!"{p} : Nat"
    else do
      unless !f.required do die s!"{it.id}.{f.yaml}: required float number is unhandled — narrow it in `natNumberFields` or extend the generator"
      return s!"{p} : Option Float := none"
  | "integer" =>
    unless f.required do die s!"{it.id}.{f.yaml}: optional integer is unhandled"
    return s!"{p} : Nat"
  | "block" =>
    return s!"{p} : {f.blockType} := \{}"
  | other => die s!"{it.id}.{f.yaml}: no binder rule for field type `{other}`"

/-- Expression (a `List String` of `k: v` cells) serializing one field.
    `pref` prefixes the parameter reference (`"b."` for block projections). -/
def yamlSnippet (it : ItemInfo) (f : FieldInfo) (pref : String := "") : IO String := do
  let p := pref ++ f.param
  let k := f.yaml
  match f.ftype with
  | "selector" | "relation" | "string" | "color" | "icon-path" =>
    return if f.required then s!"[kv \"{k}\" (escStr {p})]" else s!"opt \"{k}\" escStr {p}"
  | "enum" =>
    if f.required || (f.defaultStr.isSome && !it.id.startsWith "block:") then
      return s!"[kv \"{k}\" {p}.toYamlStr]"
    else return s!"opt \"{k}\" {f.enumType}.toYamlStr {p}"
  | "enum-list" =>
    return s!"[kv \"{k}\" (yamlList ({p}.map {f.enumType}.toYamlStr))]"
  | "boolean" =>
    return s!"opt \"{k}\" toString {p}"
  | "number" =>
    if natNumberFields.contains (it.id, f.yaml) then return s!"[kv \"{k}\" (toString {p})]"
    else return s!"opt \"{k}\" fmtFloat {p}"
  | "integer" =>
    return s!"[kv \"{k}\" (toString {p})]"
  | "block" =>
    return s!"blockField \"{k}\" {p}.yamlFields"
  | other => die s!"{it.id}.{f.yaml}: no YAML rule for field type `{other}`"

/-- Bound-check expression (a `List String` of error messages) for one numeric
    field, or none when the field carries no bounds. `label` names the field in
    the message. Handles `Nat` (bare) and `Option Float` shapes. -/
def boundsSnippet (label : String) (leanIsNat : Bool) (param : String)
    (bounds : List BoundCheck) : Option String :=
  if bounds.isEmpty then none
  else
    let checks := bounds.map fun b =>
      s!"(if {b.cond} then [\"{label} {b.msg}\"] else [])"
    let body := String.intercalate " ++ " checks
    if leanIsNat then
      -- required Nat field: bind v directly
      some s!"(let v := Float.ofNat {param}; {body})"
    else
      some s!"(match {param} with | some v => {body} | none => [])"

/-! ## Enum registry -/

structure EnumInfo where
  name : String
  values : Array String
  usedBy : List String
  deriving Inhabited

def registerEnum (enums : Array EnumInfo) (name : String) (values : Array String)
    (site : String) : IO (Array EnumInfo) := do
  match enums.findIdx? (·.name == name) with
  | some i =>
    let e := enums[i]!
    unless e.values == values do
      die s!"enum `{name}` has conflicting vocabularies: {e.values} (from {e.usedBy}) vs {values} (from {site})"
    return enums.set! i { e with usedBy := e.usedBy ++ [site] }
  | none =>
    return enums.push ⟨name, values, [site]⟩

/-! ## Main generation -/

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let txt ← try IO.FS.readFile manifestPath catch _ =>
    die s!"manifest not found at {manifestPath} — run `pnpm install` in widget/ first (any `lake build` does this)"
  let m ← unwrap "manifest" (Json.parse txt)

  -- Refuse manifest shapes this generator was not written for.
  for k in objKeys m do
    unless ["language", "languageVersion", "spytialCoreVersion", "versioning",
            "document", "hold", "blocks", "items", "deprecations", "documentation"].contains k do
      die s!"unknown top-level manifest key `{k}` — extend the generator to account for it"

  let coreVersion ← jStr "manifest" m "spytialCoreVersion"
  let langVersion ← jStr "manifest" m "languageVersion"

  -- hold
  let holdJ ← jObj "manifest" m "hold"
  let holdValues ← jStrArr "hold" holdJ "values"
  unless holdValues == #["always", "never"] do
    die s!"hold.values changed to {holdValues} — the generated `holdFields` emission assumes always/never"
  let holdDefault ← jStr "hold" holdJ "default"
  unless holdDefault == "always" do
    die s!"hold.default changed to `{holdDefault}`"
  let holdSupported ← jStrArr "hold" holdJ "supportedBy"
  let holdNote ← jOptStr "hold" holdJ "note"

  -- blocks
  let blocksJ ← jArr "manifest" m "blocks"
  let mut blocks : Array (String × Option String × Array FieldInfo) := #[]
  for bj in blocksJ do
    let bname ← jStr "blocks" bj "name"
    let bdesc ← jOptStr bname bj "description"
    let bfieldsJ ← jArr bname bj "fields"
    let bfields ← bfieldsJ.mapM (parseField s!"block:{bname}" bname)
    blocks := blocks.push (bname, bdesc, bfields)

  -- items
  let itemsJ ← jArr "manifest" m "items"
  let mut items : Array ItemInfo := #[]
  for ij in itemsJ do
    let id ← jStr "items" ij "id"
    let some ctor := ctorName id
      | die s!"item `{id}` has no constructor name in `ctorName` — a new spytial-core form; add it"
    let yamlKey ← jStr id ij "yamlKey"
    let sections ← jStrArr id ij "sections"
    let isConstraint ← match sections with
      | #["constraints"] => pure true
      | #["directives"] => pure false
      | s => die s!"item `{id}` has unexpected sections {s}"
    let valueShape ← jStr id ij "valueShape"
    let scalar ← match valueShape with
      | "mapping" => pure false
      | "scalar" => pure true
      | s => die s!"item `{id}` has unhandled valueShape `{s}`"
    let supportsHold := (← jOptBool id ij "supportsHold").getD false
    unless supportsHold == holdSupported.contains id do
      die s!"item `{id}`: supportsHold disagrees with hold.supportedBy"
    let fieldsJ ← jArr id ij "fields"
    let fields ← fieldsJ.mapM (parseField id id)
    if scalar && fields.size != 1 then
      die s!"scalar item `{id}` has {fields.size} fields; expected exactly 1"
    items := items.push {
      id, yamlKey, ctor, isConstraint, scalar, supportsHold, fields
      description := ← jOptStr id ij "description"
    }

  -- deprecations
  let depsJ ← jArr "manifest" m "deprecations"
  let mut itemDeps : List (String × String) := []       -- item id → message
  let mut fieldDeps : List (String × String × String) := []  -- (item, field, replacedBy)
  for dj in depsJ do
    let did ← jStr "deprecations" dj "id"
    let kind ← jStr did dj "kind"
    let reason := (← jOptStr did dj "reason").getD ""
    let replacedBy := (← jOptStr did dj "replacedBy").getD ""
    match kind with
    | "item" =>
      let path ← jStr did dj "path"
      -- `path` is the yamlKey; `id` is the manifest item id
      let some it := items.find? (·.id == did)
        | die s!"deprecation `{did}`: no such item"
      let _ := path
      itemDeps := itemDeps ++ [(it.id, s!"`{it.id}` is deprecated — use `{replacedBy}`. {reason}")]
    | "field" =>
      let path ← jStr did dj "path"
      match path.splitOn "." with
      | [item, field] => fieldDeps := fieldDeps ++ [(item, field, replacedBy)]
      | _ => die s!"deprecation `{did}`: unhandled field path `{path}`"
    | "placement" =>
      -- size/hideAtom under `directives`. The generated serializer always
      -- partitions by `isConstraint`, so the deprecated placement is never
      -- emitted; nothing to generate.
      unless ["size@directives", "hideAtom@directives"].contains did do
        die s!"deprecation `{did}`: unknown placement deprecation — check the serializer still avoids it"
    | other => die s!"deprecation `{did}`: unhandled kind `{other}`"

  -- consistency: every field the manifest marks deprecated has a deprecations entry, and vice versa
  for it in items do
    for f in it.fields do
      if f.deprecatedFor.isSome && !fieldDeps.any (fun (i, fl, _) => i == it.id && fl == f.yaml) then
        die s!"{it.id}.{f.yaml} is marked deprecated inline but has no deprecations[] entry"
  for (item, field, _) in fieldDeps do
    let some it := items.find? (·.id == item)
      | die s!"field deprecation on unknown item `{item}`"
    unless (it.fields.find? (·.yaml == field)).isSome do
      die s!"field deprecation on unknown field `{item}.{field}`"

  -- enum registry (stable, first-seen order; conflicting vocabularies die)
  let mut enums : Array EnumInfo := #[]
  for (bname, _, bfields) in blocks do
    for f in bfields do
      if f.ftype == "enum" then
        enums ← registerEnum enums f.enumType f.values s!"{bname}.{f.yaml}"
  for it in items do
    for f in it.fields do
      if f.ftype == "enum" || f.ftype == "enum-list" then
        enums ← registerEnum enums f.enumType f.values s!"{it.id}.{f.yaml}"

  -- every block referenced by an item must exist
  for it in items do
    for f in it.fields do
      if f.ftype == "block" then
        unless blocks.any (fun (b, _, _) => b.capitalize == f.blockType) do
          die s!"{it.id}.{f.yaml}: references unknown block `{f.yaml}`"

  -- ---------------------------------------------------------------- emit
  let mut L : Array String := #[]
  L := L ++ #[
    "/-",
    "@generated by `lake exe specCodegen` — do not edit by hand.",
    "",
    s!"Source: spytial-core {coreVersion}, layout-spec language {langVersion}",
    "        (widget/node_modules/spytial-core/docs/spytial-language.json,",
    "        pinned by widget/pnpm-lock.yaml to the same release as the",
    "        embedded renderer)",
    "Regenerate: just gen-spec        Drift check: just check-spec",
    "",
    "Optional fields default to unset and are omitted from the emitted YAML, so",
    "spytial-core's own defaults apply. Enum parameters with a manifest default",
    "bake it as a Lean default argument and always emit, so the traversal order",
    "or edge direction is stated at the authoring site.",
    "-/",
    "module",
    "",
    "public import Lean",
    "",
    "namespace SpytialLean",
    "",
    s!"/-- The spytial-core release this surface was generated from. -/",
    s!"public meta def specCoreVersion : String := \"{coreVersion}\"",
    "",
    s!"/-- The date the layout-spec language last changed, per the manifest. -/",
    s!"public meta def specLanguageVersion : String := \"{langVersion}\"",
    ""
  ]

  -- enums
  for e in enums do
    L := L.push s!"/-- Closed vocabulary for {String.intercalate ", " (e.usedBy.map fun u => s!"`{u}`")}. -/"
    L := L.push s!"public meta inductive {e.name} where"
    L := L.push ("  | " ++ String.intercalate " | " (e.values.toList.map valueCtor))
    L := L.push "  deriving Repr, DecidableEq, Inhabited"
    L := L.push ""
    L := L.push s!"private meta def {e.name}.toYamlStr : {e.name} → String"
    for v in e.values do
      L := L.push s!"  | .{valueCtor v} => \"{v}\""
    L := L.push ""

  -- Hold
  L := L ++ #[
    s!"/-- {sanitizeDoc (holdNote.getD "Constraint negation.")} -/",
    "public meta inductive Hold where",
    "  | always | never",
    "  deriving Repr, DecidableEq, Inhabited",
    ""
  ]

  -- serialization helpers
  L := L ++ #[
    "/-! ## YAML emission helpers",
    "",
    "Each op serializes to one flow-style YAML list item, e.g.",
    "`  - orientation: {selector: \"edges\", directions: [above]}`.",
    "Strings are JSON-escaped (JSON is a subset of YAML flow style). -/",
    "",
    "private meta def escStr (s : String) : String := (Lean.Json.str s).compress",
    "",
    "private meta def kv (k v : String) : String := k ++ \": \" ++ v",
    "",
    "private meta def flow (cells : List String) : String :=",
    "  \"{\" ++ String.intercalate \", \" cells ++ \"}\"",
    "",
    "private meta def yamlList (vs : List String) : String :=",
    "  \"[\" ++ String.intercalate \", \" vs ++ \"]\"",
    "",
    "private meta def opt {α : Type} (k : String) (f : α → String) : Option α → List String",
    "  | some v => [kv k (f v)]",
    "  | none => []",
    "",
    "private meta def blockField (k : String) (cells : List String) : List String :=",
    "  if cells.isEmpty then [] else [kv k (flow cells)]",
    "",
    "private meta def holdFields : Hold → List String",
    "  | .never => [kv \"hold\" \"never\"]",
    "  | .always => []",
    "",
    "/-- Render a positive float without the noise `toString` appends (`2.000000`). -/",
    "private meta def fmtFloat (f : Float) : String :=",
    "  let s := toString f",
    "  if s.contains '.' then",
    "    let cs := s.toList.reverse.dropWhile (· == '0')",
    "    let cs := if cs.head? == some '.' then cs.drop 1 else cs",
    "    String.ofList cs.reverse",
    "  else s",
    ""
  ]

  -- blocks: structure + yamlFields + validate
  for (bname, bdesc, bfields) in blocks do
    let ty := bname.capitalize
    L := L ++ docComment "" bdesc
    L := L.push s!"public meta structure {ty} where"
    for f in bfields do
      L := L ++ docComment "  " f.description
      let sig ← paramSig { id := s!"block:{bname}", yamlKey := bname, ctor := "", isConstraint := false,
                           scalar := false, supportsHold := false, fields := #[] } f
      L := L.push s!"  {sig}"
    L := L.push "  deriving Repr, Inhabited"
    L := L.push ""
    -- yamlFields
    L := L.push s!"private meta def {ty}.yamlFields (b : {ty}) : List String :="
    let snippets ← bfields.mapM fun f =>
      yamlSnippet { id := s!"block:{bname}", yamlKey := bname, ctor := "", isConstraint := false,
                    scalar := false, supportsHold := false, fields := #[] } f (pref := "b.")
    L := L.push ("  " ++ String.intercalate " ++ " snippets.toList)
    L := L.push ""
    -- validate (only when some field carries bounds)
    let checked := bfields.toList.filterMap fun f =>
      boundsSnippet s!"{bname}.{f.yaml}" false s!"b.{f.param}" f.bounds
    unless checked.isEmpty do
      L := L.push s!"private meta def {ty}.validate (b : {ty}) : List String :="
      L := L.push ("  " ++ String.intercalate " ++ " checked)
      L := L.push ""

  let blockHasValidate (blockType : String) : Bool :=
    blocks.any fun (bname, _, bfields) =>
      bname.capitalize == blockType && bfields.any (!·.bounds.isEmpty)

  -- SpytialOp
  L := L ++ #[
    "/-- A single Spytial operation — either a constraint (structural layout) or a",
    "    directive (presentation). Generated from spytial-core's language manifest;",
    "    one constructor per form the layout-spec parser reads. -/",
    "public meta inductive SpytialOp where"
  ]
  for it in items do
    let dep := itemDeps.find? (·.1 == it.id) |>.map (·.2)
    let doc := match it.description, dep with
      | some d, some w => some (d ++ " **Deprecated:** " ++ w)
      | some d, none => some d
      | none, some w => some ("**Deprecated:** " ++ w)
      | none, none => none
    L := L ++ docComment "  " doc
    let mut binders : Array String := #[]
    for f in it.fields do
      binders := binders.push s!"({← paramSig it f})"
    if it.supportsHold then
      binders := binders.push "(hold : Hold := .always)"
    L := L.push s!"  | {it.ctor} {String.intercalate " " binders.toList}"
  L := L ++ #["  deriving Repr, Inhabited", ""]

  -- isConstraint
  L := L ++ #[
    "/-- Is this op a constraint (emitted under `constraints:`)? `size` and",
    "    `hideAtom` are constraints; their old placement under `directives` is",
    "    deprecated upstream and never emitted here. -/",
    "public meta def SpytialOp.isConstraint : SpytialOp → Bool"
  ]
  let constraintCtors := items.toList.filter (·.isConstraint) |>.map fun it => s!".{it.ctor} .."
  L := L.push s!"  | {String.intercalate " | " constraintCtors} => true"
  L := L.push "  | _ => false"
  L := L.push ""

  -- toYamlLine
  L := L ++ #[
    "/-- Render one op as a YAML list item (a single line, flow style). -/",
    "public meta def SpytialOp.toYamlLine : SpytialOp → String"
  ]
  for it in items do
    let params := it.fields.toList.map (·.param) ++ (if it.supportsHold then ["hold"] else [])
    let pat := s!".{it.ctor} {String.intercalate " " params}"
    if it.scalar then
      let some f := it.fields[0]? | die s!"scalar item `{it.id}` has no field"
      L := L.push s!"  | {pat} => \"  - {it.yamlKey}: \" ++ {f.param}.toYamlStr"
    else
      let mut cells : Array String := #[]
      for f in it.fields do
        cells := cells.push (← yamlSnippet it f)
      if it.supportsHold then
        cells := cells.push "holdFields hold"
      L := L.push s!"  | {pat} =>"
      L := L.push s!"    \"  - {it.yamlKey}: \" ++ flow ({String.intercalate " ++ " cells.toList})"
  L := L.push ""

  -- validate
  L := L ++ #[
    "/-- Author-time checks the manifest states outright: numeric bounds and",
    "    `orientation`'s mutually-exclusive direction rules. spytial-core mostly",
    "    does *not* complain about these — an out-of-range leaf is dropped",
    "    silently — so elaboration is where they can fail loudly. -/",
    "public meta def SpytialOp.validate : SpytialOp → List String"
  ]
  let mut anyValidate := false
  for it in items do
    let mut parts : Array String := #[]
    let mut used : Array String := #[]
    for f in it.fields do
      let isNat := (f.ftype == "number" && natNumberFields.contains (it.id, f.yaml)) || f.ftype == "integer"
      if let some snip := boundsSnippet s!"{it.id}: {f.yaml}" isNat f.param f.bounds then
        parts := parts.push snip
        used := used.push f.param
      if f.ftype == "block" && blockHasValidate f.blockType then
        parts := parts.push s!"{f.param}.validate"
        used := used.push f.param
      if let some rules := f.listRules then
        for rk in objKeys rules do
          match rk with
          | "atMostOneOf" =>
            let groups ← jArr s!"{it.id}.{f.yaml}.listRules" rules "atMostOneOf"
            for gj in groups do
              let vs ← unwrap s!"{it.id} atMostOneOf" gj.getArr?
              let names ← vs.mapM fun v => unwrap s!"{it.id} atMostOneOf[]" v.getStr?
              let ctors := names.toList.map fun v => s!"{f.enumType}.{valueCtor v}"
              let quoted := String.intercalate "/" (names.toList.map fun v => s!"'{v}'")
              parts := parts.push
                s!"(if (([{String.intercalate ", " ctors}] : List {f.enumType}).filter ({f.param}.contains ·)).length > 1 then [\"{it.id}: {f.yaml} may contain at most one of {quoted}\"] else [])"
              used := used.push f.param
          | "narrowsListTo" =>
            let narrowing ← jObj s!"{it.id}.{f.yaml}.listRules" rules "narrowsListTo"
            for trigger in objKeys narrowing do
              let allowed ← jStrArr s!"{it.id} narrowsListTo" narrowing trigger
              let ctors := allowed.toList.map fun v => s!"{f.enumType}.{valueCtor v}"
              let quoted := String.intercalate "/" (allowed.toList.map fun v => s!"'{v}'")
              parts := parts.push
                s!"(if {f.param}.contains .{valueCtor trigger} && !{f.param}.all (fun d => ([{String.intercalate ", " ctors}] : List {f.enumType}).contains d) then [\"{it.id}: '{trigger}' may only be combined with {quoted}\"] else [])"
              used := used.push f.param
          | other => die s!"{it.id}.{f.yaml}: unhandled listRules key `{other}`"
    unless parts.isEmpty do
      anyValidate := true
      let pat := it.fields.toList.map (fun f => if used.contains f.param then f.param else "_")
        ++ (if it.supportsHold then ["_"] else [])
      L := L.push s!"  | .{it.ctor} {String.intercalate " " pat} =>"
      L := L.push ("    " ++ String.intercalate " ++ " parts.toList)
  let _ := anyValidate
  L := L.push "  | _ => []"
  L := L.push ""

  -- deprecationWarning
  L := L ++ #[
    "/-- A warning when the op (or a field it sets) is a form spytial-core has",
    "    deprecated. Deprecated forms keep parsing and keep their meaning; they are",
    "    removed only in a major release of spytial-core. -/",
    "public meta def SpytialOp.deprecationWarning : SpytialOp → Option String"
  ]
  for (id, msg) in itemDeps do
    let some it := items.find? (·.id == id) | die s!"deprecated item `{id}` vanished"
    L := L.push s!"  | .{it.ctor} .. => some \"{msg.replace "\"" "'"}\""
  -- field-level deprecations, grouped by item
  let fieldDepItems := (fieldDeps.map (·.1)).eraseDups
  for item in fieldDepItems do
    if itemDeps.any (·.1 == item) then
      die s!"item `{item}` has both item- and field-level deprecations; the generated match arms would shadow"
    let some it := items.find? (·.id == item) | die s!"field deprecation on unknown item `{item}`"
    let deps := fieldDeps.filter (·.1 == item)
    let depFields := deps.map (·.2.1)
    let pat := it.fields.toList.map (fun f => if depFields.contains f.yaml then f.param else "_")
      ++ (if it.supportsHold then ["_"] else [])
    let cond := String.intercalate " || " (deps.map fun (_, f, _) =>
      s!"{paramName item f}.isSome")
    let rewrites := String.intercalate ", " (deps.map fun (_, f, r) => s!"{f} -> {r}")
    L := L.push s!"  | .{it.ctor} {String.intercalate " " pat} =>"
    L := L.push s!"    if {cond} then some \"{item}: flat style fields are deprecated ({rewrites})\" else none"
  L := L.push "  | _ => none"
  L := L.push ""
  L := L.push "end SpytialLean"

  let out := String.intercalate "\n" L.toList ++ "\n"

  if check then
    let existing ← try IO.FS.readFile outputPath catch _ => pure ""
    if existing == out then
      IO.println s!"{outputPath} is up to date (spytial-core {coreVersion}, language {langVersion})."
      return 0
    else
      IO.eprintln s!"{outputPath} is stale — run `just gen-spec` and commit the diff."
      return 1
  else
    IO.FS.writeFile outputPath out
    IO.println s!"wrote {outputPath} (spytial-core {coreVersion}, language {langVersion})."
    return 0

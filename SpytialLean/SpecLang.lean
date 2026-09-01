module

public import Lean
public meta import SpytialLean.ManifestJson

namespace SpytialLean.SpecLang

open Lean Elab Command SpytialLean.ManifestJson

/-! # The op surface, read off its manifest

The op surface spytial-lean accepts *is* spytial-core's layout-spec language:
the commands below parse `docs/spytial-language.json` from the resolved package
and declare the id enumerations and tables. `docs/language-manifests.md` is the
design story. -/

-- The widget is what depends on spytial-core, so pnpm resolves it under there.
private meta def manifestText : String :=
  include_str ".." / "widget" / "node_modules" / "spytial-core" / "docs" /
    "spytial-language.json"

/-! ## The language as data, with ids still strings -/

json_union DeclaredArity where
  | unary
  | binary
  | "n-ary" => nary

deriving instance DecidableEq for DeclaredArity

public meta structure Bound where
  value : JsonNumber
  exclusive : Bool
  deriving Repr, Inhabited

/-- `atMostOneOf` forbids two values from the same set; choosing a key of
    `narrows` restricts the whole list to the named values. -/
public meta structure EnumListRules where
  atMostOneOf : List (List String)
  narrows : List (String × List String)
  deriving Repr, Inhabited

json_union ValueShape where
  | mapping
  | scalar

json_union Section where
  | constraints
  | directives

public meta structure JAccept where
  arity : DeclaredArity
  minColumns : Nat
  maxColumns : Option Nat
  requires : Option String
  deriving Repr, Inhabited

json_record JAccept ignoring "meaning"

json_union JFieldType on "type" where
  | selector (arity : DeclaredArity) (accepts : List JAccept)
  | relation
  | "string" => str
  | «enum» (values : List String) (default : Option String)
  | "enum-list" => enumList (values : List String) (listRules : Option JsonObject)
  | number (minimum : Option JsonNumber) (exclusiveMinimum : Option JsonNumber)
      (maximum : Option JsonNumber) (exclusiveMaximum : Option JsonNumber)
  | boolean (default : Option Bool)
  | block (block : String)
  | "icon-path" => iconPath
  | color

json_union JAltField on "type" where
  | «enum» (name : String)
  | block (name : String) (block : String)

public meta structure JAltForm where
  «type» : String
  fields : List JAltField
  deriving Inhabited

json_record JAltForm ignoring "description"

public meta structure JDeprecated where
  replacedBy : String
  deriving Inhabited

-- an item's rewrite hints (`mapping`, `reason`, `warningSpecType`) are core's own
json_record JDeprecated ignoring "mapping" "reason" "warningSpecType"

/-- Read off the same object as `JFieldType`, which takes the rest. -/
public meta structure JField where
  name : String
  required : Option Bool
  alternativeForm : Option JAltForm
  deprecated : Option JDeprecated
  deriving Inhabited

-- `pattern` and `enforcement` are the engine's own value checks
json_record JField ignoring JFieldType.memberNames "description" "note" "pattern"
  "enforcement"

public meta structure JItem where
  id : String
  yamlKey : Option String
  sections : Option (List Section)
  valueShape : Option ValueShape
  supportsHold : Option Bool
  fields : Option (List Json)
  deprecated : Option JDeprecated
  deriving Inhabited

-- `discriminator` and the section-deprecation pair steer core's YAML reader
json_record JItem ignoring "description" "example" "label" "note" "discriminator"
  "deprecatedSections" "sectionDeprecation"

public meta structure JBlock where
  name : String
  fields : List Json
  deriving Inhabited

json_record JBlock ignoring "description"

public meta structure JHold where
  field : String
  values : List String
  default : String
  supportedBy : List String
  deriving Inhabited

json_record JHold ignoring "note"

/-- `supportedBy` is where core parses the provenance stamp, `displayedBy`
    where it reads it back out. -/
public meta structure JSource where
  field : String
  fields : List Json
  supportedBy : List String
  displayedBy : List String
  deriving Inhabited

json_record JSource ignoring "note"

public meta structure JDocument where
  sections : List Section
  deriving Inhabited

json_record JDocument ignoring "notes" "sectionShape" "unknownKeys"

public meta structure JManifest where
  document : JDocument
  hold : JHold
  source : JSource
  blocks : List JBlock
  deriving Inhabited

-- `items` and `languageVersion` are read on their own; `deprecations` restates
-- what `items[].deprecated` already reads
json_record JManifest ignoring "items" "language" "languageVersion"
  "spytialCoreVersion" "documentation" "versioning" "deprecations"

/-! ## Choices the manifest leaves open

The manifest describes core's YAML surface; how its fields lay out as Lean
arguments is this package's own choice. -/

/-- Items where an optional selector may lead the argument list even though the
    manifest does not list it first: `size (lo) 30 20` reads better than
    `size 30 20 (lo)`. -/
private meta def leadingSelectorOverride : List String := ["size"]

private meta def boolSugarTable : List (String × String × Bool) :=
  [("labels", "showLabel", true), ("noLabels", "showLabel", false)]

/-! ## Facts the manifest does not carry yet

Proposed upstream as spytial-core#580 and #581, and tables here until a
release carries them. Each is keyed by manifest ids and checked against the
live manifest at derivation, and all of them hold only for the language they
were audited against, so a language bump fails the build until they are read
again. -/

private meta def tablesLanguageVersion : String := "2026-08-25"

/-- How many columns a graph-side name of each kind has. -/
private meta def introducedKindsTable : List (String × Nat) := [("group", 1), ("edge", 2)]

/-- The string positions that name a group or an inferred edge: the kind named
    and the `item.field` positions where the engine resolves such a name. -/
private meta def introducesTable : List ((String × String) × String × List String) :=
  [(("group", "name"), "group", ["inferredEdge.draw", "edgeStyle.field"]),
   (("inferredEdge", "name"), "edge", ["edgeStyle.field"])]

/-- Items whose listed fields are their entire effect: an instance setting none
    of them parses and does nothing. -/
private meta def inertWhenBareTable : List (String × List String) :=
  [("atomStyle", ["fillStyle", "borderStyle", "iconStyle", "textStyle", "showLabel"]),
   ("edgeStyle", ["lineStyle", "textStyle", "showLabel", "hidden"])]

/-- What the engine does with the columns between a tuple's first and last. -/
private meta inductive MiddleColumns where
  | ignored
  | displayed

/-- Per selector position admitting more than two columns. -/
private meta def middleColumnsTable : List ((String × String) × MiddleColumns) :=
  [(("orientation", "selector"), .ignored), (("align", "selector"), .ignored),
   (("cyclic", "selector"), .ignored), (("group", "selector"), .ignored),
   (("edgeStyle", "filter"), .ignored), (("attribute", "filter"), .ignored),
   (("hideField", "filter"), .ignored), (("tag", "value"), .displayed),
   (("inferredEdge", "selector"), .displayed)]

/-! ## Assembling the tables' input -/

private meta structure RawSelForm where
  min : Nat
  max : Option Nat
  requires : Option String
  middlesIgnored : Bool

private meta inductive RawFieldType where
  | selector (forms : List RawSelForm)
  | relation
  | str
  | «enum» (values : List String) (dflt : Option String)
  | enumList (values : List String) (rules : EnumListRules)
  | number (min : Option Bound) (max : Option Bound)
  | boolean (dflt : Option Bool)
  | block (blockId : String)
  | iconPath
  | color

private meta def RawFieldType.isBlock : RawFieldType → Bool
  | .block _ => true | _ => false

private meta structure RawAltForm where
  enumField : String
  /-- Field name × block name. -/
  blocks : List (String × String)

private meta structure RawIntroduces where
  field : String
  arity : Nat
  referencedBy : List String

private meta structure RawField where
  name : String
  type : RawFieldType
  required : Bool
  alt : Option RawAltForm
  introduces : Option RawIntroduces

private meta structure RawItem where
  id : String
  yamlKey : String
  constraint : Bool
  scalar : Bool
  supportsHold : Bool
  fields : List RawField
  positional : List String
  leadingSelector : Option String
  introduces : Option RawIntroduces
  effectFields : List String
  displaysSource : Bool

private meta structure RawBlock where
  name : String
  fields : List RawField

private meta structure RawManifest where
  lexical : JManifest
  items : List RawItem
  blocks : List RawBlock
  fieldIds : List String
  deprecatedItems : List (String × String)
  deprecatedFields : List (String × String)

private meta def listRules (o : JsonObject) : Except String EnumListRules := do
  onlyMembers ["atMostOneOf", "narrowsListTo"] o
  let atMostOneOf : List (List String) := (← o.get? "atMostOneOf").getD []
  let narrows : JsonObject := (← o.get? "narrowsListTo").getD ∅
  return { atMostOneOf, narrows := ← narrows.toArray.toList.mapM fun (key, allowed) => do
    return (key, ← (fromJson? allowed).mapError fun e => s!"narrowsListTo.{key}: {e}") }

private meta def bound (incl excl : Option JsonNumber) : Except String (Option Bound) :=
  match incl, excl with
  | some _, some _ => .error "both an inclusive and an exclusive bound"
  | some n, none => .ok (some ⟨n, false⟩)
  | none, some n => .ok (some ⟨n, true⟩)
  | none, none => .ok none

/-- The column bounds are what the elaborator uses, so a disagreement with the
    arity word means one of the two moved upstream and this reading is stale. -/
private meta def selForm (middle? : Option MiddleColumns) (a : JAccept) :
    Except String RawSelForm := do
  let agrees := match a.arity with
    | .unary => a.minColumns == 1 && a.maxColumns == some 1
    | .binary => a.minColumns == 2 && a.maxColumns == some 2
    | .nary => 2 ≤ a.minColumns && a.maxColumns.isNone
  unless agrees do
    .error s!"an accepted form's arity word and its column bounds \
      ({a.minColumns}, {repr a.maxColumns}) disagree"
  if a.maxColumns.all (2 < ·) && middle?.isNone then
    .error s!"an accepted form admitting more than two columns \
      ({a.minColumns}, {repr a.maxColumns}) has no middleColumnsTable entry \
      saying what becomes of the middle ones"
  return { min := a.minColumns, max := a.maxColumns, requires := a.requires,
           middlesIgnored := middle? matches some .ignored }

private meta def altForm (a : JAltForm) : Except String RawAltForm := do
  unless a.type == "block" do .error "alternativeForm is not a block"
  let enums := a.fields.filterMap fun | .«enum» n => some n | _ => none
  let blocks := a.fields.filterMap fun | .block n b => some (n, b) | _ => none
  match enums with
  | [e] => return { enumField := e, blocks }
  | [] => .error "alternativeForm has no enum field"
  | _ => .error "two enum fields in alternativeForm"

private meta def decodeFields (js : List Json) : Except String (List (JField × Json)) :=
  js.mapM fun j => do return (← fromJson? j, j)

/-- `c` is `j`'s `JField` reading; `JFieldType` takes the rest of the object. -/
private meta def fieldOf (itemId : String) (c : JField) (j : Json) :
    Except String (Option RawField) := do
  -- A deprecated field keeps parsing upstream; the new surface never writes it.
  if c.deprecated.isSome then return none
  let name := c.name
  let here (e : String) : String := s!"{itemId}.{name}: {e}"
  let ty : JFieldType ← (fromJson? j).mapError here
  let alt ← match c.alternativeForm with
    | some a => some <$> (altForm a).mapError here
    | none => pure none
  let middle? := middleColumnsTable.lookup (itemId, name)
  let type : RawFieldType ← match ty with
    | .selector arity accepts =>
      let some first := accepts.head?
        | .error (here "a selector position with no accepted form")
      unless first.arity == arity do
        .error (here "the declared arity is not the first accepted form's")
      pure (.selector (← (accepts.mapM (selForm middle?)).mapError here))
    | .relation => pure .relation
    | .str => pure .str
    | .«enum» values dflt => pure (.«enum» values dflt)
    | .enumList values rules =>
      pure (.enumList values (← match rules with
        | some o => (listRules o).mapError here
        | none => pure { atMostOneOf := [], narrows := [] }))
    | .number mn xmn mx xmx =>
      pure (.number (← (bound mn xmn).mapError here) (← (bound mx xmx).mapError here))
    | .boolean dflt => pure (.boolean dflt)
    | .block b => pure (.block b)
    | .iconPath => pure .iconPath
    | .color => pure .color
  if alt.isSome && !(type matches RawFieldType.«enum» ..) then
    .error (here "alternativeForm on a non-enum field")
  if middle?.isSome then
    match type with
    | .selector forms =>
      if forms.all fun f => f.max.any (· ≤ 2) then
        .error (here "middleColumnsTable names a position capped at two columns")
    | _ => .error (here "middleColumnsTable names a position that is not a selector")
  let introduces ← (introducesTable.lookup (itemId, name)).mapM fun (kind, referencedBy) => do
    unless type matches RawFieldType.str do
      .error (here "a field introducing a graph-side name must be a string")
    let some arity := introducedKindsTable.lookup kind
      | .error (here s!"introducesTable names the kind {kind.quote}, which \
          introducedKindsTable does not declare")
    return { field := name, arity, referencedBy }
  return some { name, type, required := c.required.getD false, alt, introduces }

/-- `fieldPaths` and the deprecation pairs cover deprecated surface; `item` leaves it out. -/
private meta structure ParsedItem where
  fieldPaths : List String
  deprecatedItem : Option (String × String)
  deprecatedFields : List (String × String)
  item : Option RawItem

private meta def itemOf (displayedBy : List String) (j : Json) :
    Except String ParsedItem := do
  let i : JItem ← fromJson? j
  let id := i.id
  let here (e : String) : String := s!"{id}: {e}"
  let jfields ← decodeFields (i.fields.getD [])
  let fieldPaths := jfields.map fun (f, _) => s!"{id}.{f.name}"
  if let some d := i.deprecated then
    return { fieldPaths, deprecatedItem := some (id, d.replacedBy),
             deprecatedFields := [], item := none }
  let deprecatedFields := jfields.filterMap fun (f, _) =>
    f.deprecated.map fun d => (s!"{id}.{f.name}", d.replacedBy)
  let some yamlKey := i.yamlKey | .error (here "no yamlKey")
  let constraint ← match i.sections with
    | some [.constraints] => pure true
    | some [.directives] => pure false
    | s => .error (here s!"no representation for sections {repr s}")
  let some shape := i.valueShape | .error (here "no valueShape")
  let fields ← jfields.filterMapM fun (c, fj) => fieldOf id c fj
  -- A scalar item serializes as its one field's value (`Spec.lean`), leaving
  -- nowhere for a second field, a `hold`, or the source stamp riding beside.
  let scalar := shape matches .scalar
  let supportsHold := i.supportsHold.getD false
  let displaysSource := displayedBy.contains id
  if scalar then
    unless fields.length == 1 do
      .error (here s!"no representation for a scalar item with {fields.length} fields")
    if supportsHold then
      .error (here "no representation for a scalar item that supports hold")
    if displaysSource then
      .error (here "no representation for a scalar item that displays its source stamp")
  for f in fields do
    if f.required && f.type.isBlock then
      .error s!"{id}.{f.name}: a required block has no positional surface"
  for f in fields do
    if let .selector forms := f.type then
      for r in forms.filterMap (·.requires) do
        unless fields.any (·.name == r) do
          .error s!"{id}.{f.name}: an accepted form requires {r.quote}, which \
            the item does not have"
  let positional := (fields.filter (·.required)).map (·.name)
  -- A variadic enum-list swallows the rest of the argument list.
  for (f, k) in positional.zipIdx do
    if (fields.find? (·.name == f)).any (·.type matches RawFieldType.enumList ..) then
      unless k == positional.length - 1 do
        .error s!"{id}.{f}: a required enum-list must be the last positional field"
  let leadingSelector ←
    if leadingSelectorOverride.contains id then
      match fields.find? fun f => !f.required && f.type matches .selector _ with
      | some f => pure (some f.name)
      | none => .error (here "leadingSelectorOverride names an item with no optional selector")
    else
      pure <| match fields with
        | f :: _ => if !f.required && f.type matches .selector _ then some f.name else none
        | [] => none
  let introduces ← match fields.filterMap (·.introduces) with
    | [] => pure none
    | [i] => pure (some i)
    | is => .error (here s!"two fields introduce a name \
        ({", ".intercalate (is.map (·.field))}); an op introduces at most one")
  let inert? := inertWhenBareTable.lookup id
  let effectFields := inert?.getD []
  if inert?.isSome && effectFields.isEmpty then
    .error (here "inertWhenBareTable names no effect field, so every body would be inert")
  for f in effectFields do
    unless fields.any (·.name == f) do
      .error (here s!"inertWhenBareTable names the effect field {f.quote}, which it does not have")
  return { fieldPaths, deprecatedItem := none, deprecatedFields,
           item := some { id, yamlKey, constraint, scalar, supportsHold,
                          fields, positional, leadingSelector, introduces,
                          effectFields, displaysSource } }

private meta def blockOf (b : JBlock) : Except String RawBlock := do
  let fields ← (← decodeFields b.fields).filterMapM fun (c, j) => fieldOf b.name c j
  for f in fields do
    if f.required then
      .error s!"{b.name}.{f.name}: no representation for a required block field"
    if f.type.isBlock || f.alt.isSome then
      .error s!"{b.name}.{f.name}: blocks do not nest"
    if f.introduces.isSome then
      .error s!"{b.name}.{f.name}: a block leaf introduces no graph-side name"
  return { name := b.name, fields }

private meta def RawField.ids (f : RawField) : List String :=
  f.name :: match f.alt with
    | some a => a.enumField :: a.blocks.map (·.1)
    | none => []

private meta def parseManifest : Except String RawManifest := do
  let json ← Json.parse manifestText
  let version ← member String json "languageVersion"
  unless version == tablesLanguageVersion do
    .error s!"languageVersion is {version}, but the tables in SpecLang.lean were \
      audited against {tablesLanguageVersion}; check them against the new \
      language and move the pin"
  let m : JManifest ← fromJson? json
  let rawItems ← member (Array Json) json "items"

  unless m.document.sections matches [.constraints, .directives] do
    .error "document.sections moved; the lowering's section names are stale"

  let parsed ← rawItems.toList.mapM (itemOf m.source.displayedBy)
  let items := parsed.filterMap (·.item)
  let blocks ← m.blocks.mapM blockOf
  let sourceFields ← (← decodeFields m.source.fields).filterMapM fun (c, j) =>
    fieldOf m.source.field c j

  -- `Spec.lean`'s `OpSource` is these two fields, by name.
  unless sourceFields.map (·.name) == ["text", "location"] do
    .error s!"source.fields is {sourceFields.map (·.name)}; OpSource models \
      a text and a location"

  let deprecatedItems := parsed.filterMap (·.deprecatedItem)
  let deprecatedFields := parsed.flatMap (·.deprecatedFields)

  -- A reference site is a position in the manifest's own surface, deprecated
  -- ones included: where the engine resolves the name, not where we write it.
  let fieldPaths := parsed.flatMap (·.fieldPaths)
  for i in items do
    if let some intro := i.introduces then
      for path in intro.referencedBy do
        unless fieldPaths.contains path do
          .error s!"{i.id}.{intro.field}: introduces.referencedBy names \
            {path.quote}, which is not a field"

  for id in leadingSelectorOverride do
    unless items.any (·.id == id) do
      .error s!"leadingSelectorOverride names {id.quote}, which is not a live item"
  for (id, _) in inertWhenBareTable do
    unless items.any (·.id == id) do
      .error s!"inertWhenBareTable names {id.quote}, which is not a live item"
  for ((id, field), _) in introducesTable do
    unless items.any fun i => i.id == id && i.fields.any (·.name == field) do
      .error s!"introducesTable names {id}.{field}, which is not a live field"
  for ((id, field), _) in middleColumnsTable do
    unless items.any fun i => i.id == id && i.fields.any (·.name == field) do
      .error s!"middleColumnsTable names {id}.{field}, which is not a live field"
  for id in m.hold.supportedBy do
    unless items.any (·.id == id) || deprecatedItems.any (·.1 == id) do
      .error s!"hold.supportedBy: names {id.quote}, which is not an item"
  for id in m.source.supportedBy do
    unless items.any (·.id == id) || deprecatedItems.any (·.1 == id) do
      .error s!"source.supportedBy: names {id.quote}, which is not an item"
  for id in m.source.displayedBy do
    unless m.source.supportedBy.contains id do
      .error s!"source.displayedBy: {id.quote} is not in supportedBy"
  for (word, fname, _) in boolSugarTable do
    let carriers := items.filter fun i =>
      i.fields.any fun f => f.name == fname && f.type matches .boolean _
    if carriers.isEmpty then
      .error s!"boolSugar {word.quote} names the field {fname.quote}, \
        which no live item has"

  -- Hold support is stated twice, per item and as one list, so each side checks
  -- the other. `supportedBy` may also name a deprecated item, which this loop
  -- does not see.
  for i in items do
    let listed := m.hold.supportedBy.contains i.id
    unless i.supportsHold == listed do
      .error s!"{i.id}: items[].supportsHold is {i.supportsHold} but \
        hold.supportedBy {if listed then "lists" else "does not list"} it"

  -- Field ids are global across items, blocks and the source stamp: the same
  -- name means the same serialized key everywhere.
  let fieldIds := ((items.flatMap (·.fields) ++ blocks.flatMap (·.fields)
    ++ sourceFields).flatMap RawField.ids).eraseDups
  for i in items do
    if blocks.any (·.name == i.id) then
      .error s!"{i.id.quote} is both an item and a block; the id namespaces would collide"

  return { lexical := m, items, blocks, fieldIds, deprecatedItems, deprecatedFields }

private meta def manifest! : CommandElabM RawManifest :=
  ManifestJson.manifest! "spytial manifest" parseManifest

/-! ## The id enumerations

Generated enumerations, so a table lookup is total and a misspelling is a type
error. `fieldName` is the key a field lowers to, and its keyword spelling. -/

private meta def enumCtor : Name → String → Ident :=
  ManifestJson.enumCtor `SpytialLean.SpecLang

elab "derive_spec_ids" : command => do
  let m ← manifest!
  let itemIds := m.items.map (·.id)
  let blockIds := m.blocks.map (·.name)
  declareEnum `ItemId itemIds
  declareEnum `BlockId blockIds
  declareEnum `FieldId m.fieldIds
  declareAll `allItems `ItemId itemIds
  declareAll `allBlocks `BlockId blockIds
  declareNames `itemName `ItemId itemIds
  declareNames `blockName `BlockId blockIds
  declareNames `fieldName `FieldId m.fieldIds

derive_spec_ids

/-! ## The enum-carrying vocabulary -/

/-- The block form of an enum field (`group.addEdge`): the enum value rides
    as `enumField` beside the listed blocks. -/
public meta structure AltForm where
  enumField : FieldId
  blocks : List (FieldId × BlockId)
  deriving Repr, Inhabited

/-- One shape a selector position accepts. `requires` is a sibling field that
    has to be set alongside for the form to apply at all (`inferredEdge`'s unary
    form needs `draw`); `max` absent is no upper bound. -/
public meta structure SelForm where
  min : Nat
  max : Option Nat
  requires : Option FieldId
  /-- The engine keeps only the first and last column of a tuple this wide;
      `inferredEdge` and `tag` are the positions that instead show them. -/
  middlesIgnored : Bool
  deriving Repr, Inhabited

/-- `referencedBy` are the `item.field` positions where the engine resolves such
    a name; a reference from anywhere else is never looked up. -/
public meta structure Introduces where
  field : FieldId
  arity : Nat
  referencedBy : List String
  deriving Repr, Inhabited

public meta inductive FieldType where
  | selector (forms : List SelForm)
  /-- A relation name from the walker's vocabulary. -/
  | relation
  | str
  | «enum» (values : List String) (dflt : Option String)
  | enumList (values : List String) (rules : EnumListRules)
  | number (min : Option Bound) (max : Option Bound)
  | boolean (dflt : Option Bool)
  | block (id : BlockId)
  /-- A bundled icon name, icon-pack reference, URL, or path. -/
  | iconPath
  | color
  deriving Repr, Inhabited

public meta structure FieldSpec where
  id : FieldId
  type : FieldType
  required : Bool
  alt : Option AltForm
  deriving Repr, Inhabited

public meta structure ItemSpec where
  id : ItemId
  yamlKey : String
  /-- Lowers into the `constraints` section (else `directives`). -/
  constraint : Bool
  /-- `valueShape: scalar`: the single field's value is the whole payload. -/
  scalar : Bool
  supportsHold : Bool
  fields : List FieldSpec
  /-- Required fields in surface order; a trailing enum-list is variadic. -/
  positional : List FieldId
  /-- An optional selector that may fill the leading positional slot. -/
  leadingSelector : Option FieldId
  introduces : Option Introduces
  /-- The fields that are this item's entire effect: an instance setting none of
      them parses and does nothing, which elaboration rejects. -/
  effectFields : List FieldId
  /-- Core reads this op's `source` stamp back out, so carrying one buys a
      conflict report that quotes the author. Elsewhere the stamp is left off. -/
  displaysSource : Bool
  deriving Repr, Inhabited

public meta structure BlockSpec where
  id : BlockId
  fields : List FieldSpec
  deriving Repr, Inhabited

/-! ## The tables

`holdField`/`holdValues`/`holdDefault` are `hold: never`, which negates a
constraint; `sourceField` is the key the provenance stamp rides under. -/

private meta instance : Quote Int := ⟨fun
  | .ofNat n => Syntax.mkCApp ``Int.ofNat #[quote n]
  | .negSucc n => Syntax.mkCApp ``Int.negSucc #[quote n]⟩

private meta instance : Quote JsonNumber := ⟨fun n =>
  Syntax.mkCApp ``JsonNumber.mk #[quote n.mantissa, quote n.exponent]⟩

private meta instance : Quote Bound := ⟨fun b =>
  Syntax.mkCApp ``Bound.mk #[quote b.value, quote b.exclusive]⟩

private meta instance : Quote EnumListRules := ⟨fun r =>
  Syntax.mkCApp ``EnumListRules.mk #[quote r.atMostOneOf, quote r.narrows]⟩

private meta def quoteSelForm (f : RawSelForm) : Term :=
  Syntax.mkCApp ``SelForm.mk #[quote f.min, quote f.max,
    quote (f.requires.map fun r => (enumCtor `FieldId r : Term)),
    quote f.middlesIgnored]

private meta def quoteIntroduces (i : RawIntroduces) : Term :=
  Syntax.mkCApp ``Introduces.mk #[enumCtor `FieldId i.field, quote i.arity,
    quote i.referencedBy]

private meta def quoteFieldType : RawFieldType → Term
  | .selector fs => Syntax.mkCApp ``FieldType.selector #[quote (fs.map quoteSelForm)]
  | .relation => mkCIdent ``FieldType.relation
  | .str => mkCIdent ``FieldType.str
  | .«enum» vs d => Syntax.mkCApp ``FieldType.«enum» #[quote vs, quote d]
  | .enumList vs r => Syntax.mkCApp ``FieldType.enumList #[quote vs, quote r]
  | .number min max => Syntax.mkCApp ``FieldType.number #[quote min, quote max]
  | .boolean d => Syntax.mkCApp ``FieldType.boolean #[quote d]
  | .block b => Syntax.mkCApp ``FieldType.block #[enumCtor `BlockId b]
  | .iconPath => mkCIdent ``FieldType.iconPath
  | .color => mkCIdent ``FieldType.color

private meta def quoteAltForm (a : RawAltForm) : Term :=
  Syntax.mkCApp ``AltForm.mk #[enumCtor `FieldId a.enumField,
    quote (a.blocks.map fun (f, b) =>
      (Syntax.mkCApp ``Prod.mk #[enumCtor `FieldId f, enumCtor `BlockId b] : Term))]

private meta def quoteField (f : RawField) : Term :=
  Syntax.mkCApp ``FieldSpec.mk #[enumCtor `FieldId f.name, quoteFieldType f.type,
    quote f.required, quote (f.alt.map quoteAltForm)]

private meta def quoteItem (i : RawItem) : Term :=
  Syntax.mkCApp ``ItemSpec.mk #[enumCtor `ItemId i.id, quote i.yamlKey,
    quote i.constraint, quote i.scalar, quote i.supportsHold,
    quote (i.fields.map quoteField),
    quote (i.positional.map fun f => (enumCtor `FieldId f : Term)),
    quote (i.leadingSelector.map fun f => (enumCtor `FieldId f : Term)),
    quote (i.introduces.map quoteIntroduces),
    quote (i.effectFields.map fun f => (enumCtor `FieldId f : Term)),
    quote i.displaysSource]

private meta def quoteBlock (b : RawBlock) : Term :=
  Syntax.mkCApp ``BlockSpec.mk #[enumCtor `BlockId b.name, quote (b.fields.map quoteField)]

elab "derive_spec_tables" : command => do
  let m ← manifest!
  declareDef `items (← `(Array ItemSpec)) (← `(#[$((m.items.map quoteItem).toArray),*]))
  declareDef `blocks (← `(Array BlockSpec)) (← `(#[$((m.blocks.map quoteBlock).toArray),*]))
  declareDef `holdField (← `(String)) (quote m.lexical.hold.field)
  declareDef `holdValues (← `(List String)) (quote m.lexical.hold.values)
  declareDef `holdDefault (← `(String)) (quote m.lexical.hold.default)
  declareDef `sourceField (← `(String)) (quote m.lexical.source.field)
  declareDef `boolSugar (← `(List (String × FieldId × Bool)))
    (quote (boolSugarTable.map fun (w, f, v) =>
      (Syntax.mkCApp ``Prod.mk #[quote w,
        Syntax.mkCApp ``Prod.mk #[enumCtor `FieldId f, quote v]] : Term)))
  declareDef `deprecatedItems (← `(List (String × String))) (quote m.deprecatedItems)
  declareDef `deprecatedFields (← `(List (String × String))) (quote m.deprecatedFields)

derive_spec_tables

/-! ## Reading the tables -/

private meta def itemTable : Std.HashMap ItemId ItemSpec :=
  items.foldl (init := {}) fun m i => m.insert i.id i

private meta def blockTable : Std.HashMap BlockId BlockSpec :=
  blocks.foldl (init := {}) fun m b => m.insert b.id b

public meta def ItemSpec.of (i : ItemId) : ItemSpec := itemTable.getD i default

public meta def BlockSpec.of (b : BlockId) : BlockSpec := blockTable.getD b default

public meta def ItemSpec.field? (i : ItemSpec) (f : FieldId) : Option FieldSpec :=
  i.fields.find? (·.id == f)

public meta def itemOfKey? (s : String) : Option ItemId :=
  allItems.find? fun i => itemName i == s

end SpytialLean.SpecLang

module

public import Lean
public meta import SpytialLean.ManifestJson

namespace SpytialLean.SpecLang

open Lean Elab Command SpytialLean.ManifestJson

/-! # The op surface, read off its manifest

The op surface spytial-lean accepts *is* spytial-core's layout-spec language:
the commands below parse `docs/spytial-language.json` from the resolved
package and declare the id enumerations and tables.
`docs/language-manifests.md` is the design story. -/

-- The widget is what depends on spytial-core, so pnpm resolves it under there.
private meta def manifestText : String :=
  include_str ".." / "widget" / "node_modules" / "spytial-core" / "docs" /
    "spytial-language.json"

/-! ## The language as data

Ids stay strings until the enumerations exist. -/

/-- The arity word an accepted form declares. Redundant with the form's own
    column bounds, which is what makes it worth cross-checking. -/
json_union DeclaredArity where
  | unary
  | binary
  | "n-ary" => nary

deriving instance DecidableEq for DeclaredArity

/-- A numeric bound, from the manifest's (exclusive)minimum/maximum. -/
public meta structure Bound where
  value : JsonNumber
  exclusive : Bool
  deriving Repr, Inhabited

/-- Validity rules for an enum-list: `atMostOneOf` forbids two values from
    the same set; choosing a key of `narrows` restricts the whole list to
    the named values. -/
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

/-- One shape a selector position accepts. `meaning` is prose the manifest
    states for a reader and is not decoded. -/
public meta structure JAccept where
  arity : DeclaredArity
  minColumns : Nat
  maxColumns : Option Nat
  /-- A sibling field that has to be set for this form to apply at all. -/
  requires : Option String
  deriving Repr, Inhabited, FromJson

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
  deriving Inhabited, FromJson

public meta structure JDeprecated where
  replacedBy : String
  deriving Inhabited, FromJson

/-- Read off the same object as `JFieldType`, which takes the rest. -/
public meta structure JField where
  name : String
  required : Option Bool
  alternativeForm : Option JAltForm
  deprecated : Option JDeprecated
  deriving Inhabited, FromJson

public meta structure JItem where
  id : String
  yamlKey : Option String
  sections : Option (List Section)
  valueShape : Option ValueShape
  supportsHold : Option Bool
  fields : Option (List Json)
  deprecated : Option JDeprecated
  deriving Inhabited, FromJson

public meta structure JBlock where
  name : String
  fields : List Json
  deriving Inhabited, FromJson

public meta structure JHold where
  field : String
  values : List String
  default : String
  supportedBy : List String
  deriving Inhabited, FromJson

public meta structure JDocument where
  sections : List Section
  deriving Inhabited, FromJson

public meta structure JManifest where
  spytialCoreVersion : String
  languageVersion : String
  document : JDocument
  hold : JHold
  blocks : List JBlock
  deriving Inhabited, FromJson

/-! ## House style

The manifest describes core's YAML surface; how its fields lay out as Lean
arguments is this package's own. Each table is keyed by manifest ids, and
`parseManifest` rejects an entry naming an id the manifest no longer has. -/

/-- Items where an optional selector may lead the argument list even though the
    manifest does not list it first. Without an entry a selector leads only
    when it is the item's first field (`atomStyle`); `size` lists it last, but
    `size (lo) 30 20` reads better than `size 30 20 (lo)`. -/
private meta def leadingSelectorOverride : List String := ["size"]

/-- The graph-side name an item introduces for later ops to reference, with its
    arity. TODO(spytial-core): the manifest types these fields as plain
    strings; that `group.name` binds a unary group and `inferredEdge.name` an
    edge label lives only in `draw`'s prose. -/
private meta def introducesTable : List (String × String × Nat) :=
  [("group", "name", 1), ("inferredEdge", "name", 2)]

/-- Directives whose optional fields are their entire effect: setting none of
    them styles nothing, which elaboration rejects. TODO(spytial-core): the
    manifest has no bit for this, and "all fields optional" does not imply it —
    `attribute` is all-optional too and is its own effect. -/
private meta def mustSetSomethingTable : List String := ["atomStyle", "edgeStyle"]

/-- Bare words that set a boolean field, where a `(showLabel false)` keyword
    would be noise. -/
private meta def boolSugarTable : List (String × String × Bool) :=
  [("labels", "showLabel", true), ("noLabels", "showLabel", false)]

/-! ## Assembling the tables' input -/

private meta structure RawSelForm where
  min : Nat
  max : Option Nat
  requires : Option String

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

private meta structure RawField where
  name : String
  type : RawFieldType
  required : Bool
  alt : Option RawAltForm

private meta structure RawItem where
  id : String
  yamlKey : String
  constraint : Bool
  scalar : Bool
  supportsHold : Bool
  fields : List RawField
  positional : List String
  leadingSelector : Option String
  introduces : Option (String × Nat)
  mustSetSomething : Bool

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

/-- An accepted form's column bounds, checked against the arity word beside
    them: the bounds are what the elaborator uses, so a disagreement means one
    of the two moved upstream and this reading is stale. -/
private meta def selForm (a : JAccept) : Except String RawSelForm := do
  let agrees := match a.arity with
    | .unary => a.minColumns == 1 && a.maxColumns == some 1
    | .binary => a.minColumns == 2 && a.maxColumns == some 2
    | .nary => 2 ≤ a.minColumns && a.maxColumns.isNone
  unless agrees do
    .error s!"an accepted form's arity word and its column bounds \
      ({a.minColumns}, {repr a.maxColumns}) disagree"
  return { min := a.minColumns, max := a.maxColumns, requires := a.requires }

private meta def altForm (a : JAltForm) : Except String RawAltForm := do
  unless a.type == "block" do .error "alternativeForm is not a block"
  let enums := a.fields.filterMap fun | .«enum» n => some n | _ => none
  let blocks := a.fields.filterMap fun | .block n b => some (n, b) | _ => none
  match enums with
  | [e] => return { enumField := e, blocks }
  | [] => .error "alternativeForm has no enum field"
  | _ => .error "two enum fields in alternativeForm"

private meta def fieldOf (itemId : String) (j : Json) : Except String (Option RawField) := do
  let c : JField ← fromJson? j
  -- A deprecated field keeps parsing upstream; the new surface never writes it.
  if c.deprecated.isSome then return none
  let name := c.name
  let here (e : String) : String := s!"{itemId}.{name}: {e}"
  let ty : JFieldType ← (fromJson? j).mapError here
  let alt ← match c.alternativeForm with
    | some a => some <$> (altForm a).mapError here
    | none => pure none
  let type : RawFieldType ← match ty with
    | .selector arity accepts =>
      let some first := accepts.head?
        | .error (here "a selector position with no accepted form")
      unless first.arity == arity do
        .error (here "the declared arity is not the first accepted form's")
      pure (.selector (← (accepts.mapM selForm).mapError here))
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
  return some { name, type, required := c.required.getD false, alt }

/-- One manifest item to a `RawItem`: decode, drop it if deprecated, then apply
    the house-style tables — positional order, the leading selector, what it
    introduces, `mustSetSomething` — checking each table entry it uses against
    the fields the item actually has. -/
private meta def itemOf (j : Json) : Except String (Option RawItem) := do
  let i : JItem ← fromJson? j
  if i.deprecated.isSome then return none
  let id := i.id
  let here (e : String) : String := s!"{id}: {e}"
  let some yamlKey := i.yamlKey | .error (here "no yamlKey")
  let constraint ← match i.sections with
    | some [.constraints] => pure true
    | some [.directives] => pure false
    | s => .error (here s!"no representation for sections {repr s}")
  let some shape := i.valueShape | .error (here "no valueShape")
  let fields ← (i.fields.getD []).filterMapM (fieldOf id)
  -- Surface order: required non-block fields positionally, in manifest order.
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
  let introduces ← match introducesTable.lookup id with
    | some (fname, ar) =>
      match fields.find? (·.name == fname) with
      | some f =>
        unless f.type matches RawFieldType.str do
          .error s!"{id}.{fname}: introduces expects a string field"
        pure (some (fname, ar))
      | none => .error (here s!"introduces names the field {fname.quote}, which it does not have")
    | none => pure none
  return some { id, yamlKey, constraint, scalar := shape matches .scalar,
                supportsHold := i.supportsHold.getD false,
                fields, positional, leadingSelector, introduces,
                mustSetSomething := mustSetSomethingTable.contains id }

private meta def blockOf (b : JBlock) : Except String RawBlock := do
  let fields ← b.fields.filterMapM (fieldOf b.name)
  for f in fields do
    if f.required then
      .error s!"{b.name}.{f.name}: no representation for a required block field"
    if f.type.isBlock || f.alt.isSome then
      .error s!"{b.name}.{f.name}: blocks do not nest"
  return { name := b.name, fields }

/-- Every id a field contributes: its own, plus the enum and block fields its
    alternative form spells. -/
private meta def RawField.ids (f : RawField) : List String :=
  f.name :: match f.alt with
    | some a => a.enumField :: a.blocks.map (·.1)
    | none => []

private meta def parseManifest : Except String RawManifest := do
  let json ← Json.parse manifestText
  let m : JManifest ← fromJson? json
  let rawItems ← member (Array Json) json "items"

  -- The document section names are load-bearing for the lowering.
  unless m.document.sections matches [.constraints, .directives] do
    .error "document.sections moved; the lowering's section names are stale"

  let items ← rawItems.toList.filterMapM itemOf
  let blocks ← m.blocks.mapM blockOf

  let mut deprecatedItems : List (String × String) := []
  let mut deprecatedFields : List (String × String) := []
  for j in rawItems do
    let i : JItem ← fromJson? j
    match i.deprecated with
    | some d => deprecatedItems := deprecatedItems ++ [(i.id, d.replacedBy)]
    | none =>
      for fj in i.fields.getD [] do
        let f : JField ← fromJson? fj
        if let some d := f.deprecated then
          deprecatedFields := deprecatedFields ++ [(s!"{i.id}.{f.name}", d.replacedBy)]

  -- Verify the house-style tables still name live manifest entries.
  for id in mustSetSomethingTable ++ leadingSelectorOverride do
    unless items.any (·.id == id) do
      .error s!"house style: a table names {id.quote}, which is not a live item"
  for id in m.hold.supportedBy do
    unless items.any (·.id == id) || deprecatedItems.any (·.1 == id) do
      .error s!"hold.supportedBy: names {id.quote}, which is not an item"
  for (word, fname, _) in boolSugarTable do
    let carriers := items.filter fun i =>
      i.fields.any fun f => f.name == fname && f.type matches .boolean _
    if carriers.isEmpty then
      .error s!"house style: boolSugar {word.quote} names the field {fname.quote}, \
        which no live item has"

  -- Hold support is per-item in the manifest but our table wants it resolved.
  let items := items.map fun i =>
    { i with supportsHold := i.supportsHold && m.hold.supportedBy.contains i.id }
  for id in m.hold.supportedBy do
    if let some i := items.find? (·.id == id) then
      unless i.supportsHold do
        .error s!"{id}: hold.supportedBy and items[].supportsHold disagree"

  -- Field ids are global across items and blocks: the same name means the same
  -- serialized key everywhere.
  let fieldIds := ((items.flatMap (·.fields) ++ blocks.flatMap (·.fields)).flatMap
    RawField.ids).eraseDups
  for i in items do
    if blocks.any (·.name == i.id) then
      .error s!"{i.id.quote} is both an item and a block; the id namespaces would collide"

  return { lexical := m, items, blocks, fieldIds, deprecatedItems, deprecatedFields }

private meta def manifest! : CommandElabM RawManifest := do
  match parseManifest with
  | .ok m => return m
  | .error e => throwError "spytial manifest: {e}"

/-! ## The id enumerations

Item, block and field ids as generated enumerations, so a table lookup is
total and a misspelling is a type error. Field ids are global: the same name
is the same serialized key wherever it appears, and `fieldName` is the key a
field lowers to (also its keyword-argument spelling). -/

private meta def enumCtor (enum : Name) (id : String) : Ident :=
  mkIdent (`SpytialLean.SpecLang ++ enum ++ Name.mkSimple id)

private meta def declareEnum (enum : Name) (ids : List String) : CommandElabM Unit := do
  let ctors ← ids.mapM fun s =>
    `(Lean.Parser.Command.ctor| | $(mkIdent (Name.mkSimple s)):ident)
  elabCommand (← `(public meta inductive $(mkIdent enum):ident where
      $(ctors.toArray)*
      deriving Repr, DecidableEq, Inhabited, Hashable))

private meta def declareAll (all enum : Name) (ids : List String) : CommandElabM Unit := do
  let refs := (ids.map (enumCtor enum)).toArray
  elabCommand (← `(public meta def $(mkIdent all):ident :
      List $(mkIdent enum):ident := [$refs,*]))

/-- The manifest's own spelling of each id, as a total function. -/
private meta def declareNames (fn enum : Name) (ids : List String) : CommandElabM Unit := do
  let alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) ← ids.toArray.mapM fun s =>
    `(Lean.Parser.Term.matchAltExpr| | $(enumCtor enum s):term => $(quote s):term)
  elabCommand (← `(public meta def $(mkIdent fn):ident (id : $(mkIdent enum):ident) :
      String := match id with $alts:matchAlt*))

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

/-- One shape a selector position accepts: the tuple widths it takes, and a
    sibling field that has to be set alongside for the form to apply at all
    (`inferredEdge`'s unary form needs `draw`). `max` absent is no upper
    bound. -/
public meta structure SelForm where
  min : Nat
  max : Option Nat
  requires : Option FieldId
  deriving Repr, Inhabited

/-- What a field holds. Drives parsing, checking, and lowering alike. -/
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
  /-- Any CSS color. -/
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
  /-- Required fields, in surface order: these are the positional
      arguments. A trailing enum-list is variadic. -/
  positional : List FieldId
  /-- An optional selector that may fill the leading positional slot. -/
  leadingSelector : Option FieldId
  /-- The graph-side name this op introduces (with arity), for later ops
      in the same spec to reference. -/
  introduces : Option (FieldId × Nat)
  /-- Reject an instance that sets none of its optional fields: they are
      its entire effect. -/
  mustSetSomething : Bool
  deriving Repr, Inhabited

public meta structure BlockSpec where
  id : BlockId
  fields : List FieldSpec
  deriving Repr, Inhabited

/-! ## The tables

One command declares them all. `items` and `blocks` are the language itself.
`holdField`/`holdValues`/`holdDefault` are `hold: never`, which negates a
constraint — item-level rather than a field, so which items take it is
`ItemSpec.supportsHold`, cross-checked above against the manifest's own
`hold.supportedBy`. `boolSugar` is the bare words above, resolved to field
ids. `deprecatedItems` and `deprecatedFields` are the account of the surface
we decline, so a coverage test can insist nothing is dropped silently. -/

private meta instance : Quote Int := ⟨fun
  | .ofNat n => Syntax.mkCApp ``Int.ofNat #[quote n]
  | .negSucc n => Syntax.mkCApp ``Int.negSucc #[quote n]⟩

private meta instance : Quote JsonNumber := ⟨fun n =>
  Syntax.mkCApp ``JsonNumber.mk #[quote n.mantissa, quote n.exponent]⟩

private meta instance : Quote Bound := ⟨fun b =>
  Syntax.mkCApp ``Bound.mk #[quote b.value, quote b.exclusive]⟩

private meta instance : Quote EnumListRules := ⟨fun r =>
  Syntax.mkCApp ``EnumListRules.mk #[quote r.atMostOneOf, quote r.narrows]⟩

-- `quote (List Term)` splices pre-built terms verbatim
private meta instance : Quote Term := ⟨id⟩

private meta def quoteSelForm (f : RawSelForm) : Term :=
  Syntax.mkCApp ``SelForm.mk #[quote f.min, quote f.max,
    quote (f.requires.map fun r => (enumCtor `FieldId r : Term))]

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
    quote (i.introduces.map fun (f, n) =>
      (Syntax.mkCApp ``Prod.mk #[enumCtor `FieldId f, quote n] : Term)),
    quote i.mustSetSomething]

private meta def quoteBlock (b : RawBlock) : Term :=
  Syntax.mkCApp ``BlockSpec.mk #[enumCtor `BlockId b.name, quote (b.fields.map quoteField)]

private meta def declareDef (name : Name) (ty val : Term) : CommandElabM Unit := do
  elabCommand (← `(public meta def $(mkIdent name):ident : $ty := $val))

elab "derive_spec_tables" : command => do
  let m ← manifest!
  declareDef `items (← `(Array ItemSpec)) (← `(#[$((m.items.map quoteItem).toArray),*]))
  declareDef `blocks (← `(Array BlockSpec)) (← `(#[$((m.blocks.map quoteBlock).toArray),*]))
  declareDef `holdField (← `(String)) (quote m.lexical.hold.field)
  declareDef `holdValues (← `(List String)) (quote m.lexical.hold.values)
  declareDef `holdDefault (← `(String)) (quote m.lexical.hold.default)
  declareDef `boolSugar (← `(List (String × FieldId × Bool)))
    (quote (boolSugarTable.map fun (w, f, v) =>
      (Syntax.mkCApp ``Prod.mk #[quote w,
        Syntax.mkCApp ``Prod.mk #[enumCtor `FieldId f, quote v]] : Term)))
  declareDef `deprecatedItems (← `(List (String × String))) (quote m.deprecatedItems)
  declareDef `deprecatedFields (← `(List (String × String))) (quote m.deprecatedFields)
  declareDef `specCoreVersion (← `(String)) (quote m.lexical.spytialCoreVersion)
  declareDef `specLanguageVersion (← `(String)) (quote m.lexical.languageVersion)

derive_spec_tables

/-! ## Reading the tables -/

public meta def ItemSpec.of (i : ItemId) : ItemSpec :=
  (items.find? (·.id == i)).getD default

public meta def BlockSpec.of (b : BlockId) : BlockSpec :=
  (blocks.find? (·.id == b)).getD default

public meta def ItemSpec.field? (i : ItemSpec) (f : FieldId) : Option FieldSpec :=
  i.fields.find? (·.id == f)

public meta def BlockSpec.field? (b : BlockSpec) (f : FieldId) : Option FieldSpec :=
  b.fields.find? (·.id == f)

/-- The item a surface keyword names. -/
public meta def itemOfKey? (s : String) : Option ItemId :=
  allItems.find? fun i => itemName i == s

/-- The block a keyword argument names, within an item's field list. -/
public meta def blockOfKey? (s : String) : Option BlockId :=
  allBlocks.find? fun b => blockName b == s

public meta def fieldOfKey? (s : String) : Option FieldId := Id.run do
  for i in allItems do
    for f in (ItemSpec.of i).fields do
      if fieldName f.id == s then return some f.id
  for b in allBlocks do
    for f in (BlockSpec.of b).fields do
      if fieldName f.id == s then return some f.id
  return none

end SpytialLean.SpecLang

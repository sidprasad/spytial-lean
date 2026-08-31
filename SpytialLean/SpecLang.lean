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

/-! ## The manifest format

`manifestVersion` (semver) versions the manifest's own member shape — which
members exist and what they mean — and a consumer that reads a member requires
the minor that introduced it. This reader needs `introducedKinds`, which 1.1
added. -/

private meta def neededMajor : Nat := 1
private meta def neededMinor : Nat := 1

/-- The leading `MAJOR.MINOR`. Those two are the whole requirement, so whatever
    follows the minor — a patch, a prerelease, build metadata — is not read. -/
private meta def majorMinor (v : String) : Option (Nat × Nat) := do
  let major :: minor :: _ := v.splitOn "." | none
  return (← major.toNat?, ← minor.toNat?)

private meta def checkFormat (version? : Option String) : Except String Unit := do
  let needed := s!"{neededMajor}.{neededMinor}"
  let some version := version?
    | .error s!"no manifestVersion, so this manifest predates format \
        versioning; this reader needs {needed} or later"
  let some (major, minor) := majorMinor version
    | .error s!"manifestVersion is {version.quote}, which does not begin with a \
        numeric MAJOR.MINOR"
  unless major == neededMajor && neededMinor ≤ minor do
    .error s!"manifestVersion is {version}; this reader needs {needed} or \
      later, within major {neededMajor}"

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

/-- What the engine does with the columns between a tuple's first and last.
    Declared exactly where a form admits a third column. -/
json_union MiddleColumns where
  | ignored
  | displayed

/-- One shape a selector position accepts. `meaning` is prose the manifest
    states for a reader and is not decoded. -/
public meta structure JAccept where
  arity : DeclaredArity
  minColumns : Nat
  maxColumns : Option Nat
  middleColumns : Option MiddleColumns
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

/-- One `introducedKinds` entry: how many columns a name of that kind has. The
    manifest's `description` is prose for a reader and is not decoded. -/
public meta structure JIntroducedKind where
  arity : Nat
  deriving Inhabited, FromJson

/-- A graph-side name a string field declares, and where the engine resolves
    it: `referencedBy` are the `item.field` paths whose values are looked up
    against names of this kind. A reference from anywhere else is not. `kind`
    is a key of `introducedKinds`, which is where its arity comes from. -/
public meta structure JIntroduces where
  kind : String
  referencedBy : List String
  deriving Inhabited, FromJson

/-- Read off the same object as `JFieldType`, which takes the rest. -/
public meta structure JField where
  name : String
  required : Option Bool
  alternativeForm : Option JAltForm
  introduces : Option JIntroduces
  deprecated : Option JDeprecated
  deriving Inhabited, FromJson

/-- The fields that are an item's entire effect, named rather than left to a
    rule the reader would have to reapply. -/
public meta structure JInertWhenBare where
  effectFields : List String
  deriving Inhabited, FromJson

public meta structure JItem where
  id : String
  yamlKey : Option String
  sections : Option (List Section)
  valueShape : Option ValueShape
  supportsHold : Option Bool
  /-- Set where the item's whole effect is the fields it names. -/
  inertWhenBare : Option JInertWhenBare
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

/-- The provenance block a generator stamps an op with. `supportedBy` is where
    core parses it, `displayedBy` where it reads it back out — the ops whose
    conflict reports quote the author's own text instead of core's rendering
    of the rule. -/
public meta structure JSource where
  field : String
  fields : List Json
  supportedBy : List String
  displayedBy : List String
  deriving Inhabited, FromJson

public meta structure JDocument where
  sections : List Section
  deriving Inhabited, FromJson

public meta structure JManifest where
  spytialCoreVersion : String
  languageVersion : String
  /-- Keys are data, so this stays an object rather than becoming a record. -/
  introducedKinds : JsonObject
  document : JDocument
  hold : JHold
  source : JSource
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

/-- Bare words that set a boolean field, where a `(showLabel false)` keyword
    would be noise. -/
private meta def boolSugarTable : List (String × String × Bool) :=
  [("labels", "showLabel", true), ("noLabels", "showLabel", false)]

/-! ## Assembling the tables' input -/

private meta structure RawSelForm where
  min : Nat
  max : Option Nat
  requires : Option String
  /-- The form admits a third column and the engine discards it. -/
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

/-- The kinds a name can be introduced as, and the arity each carries. Data
    rather than a rule restated here, so a kind added upstream needs no edit. -/
private meta abbrev IntroducedKinds := List (String × Nat)

private meta def introducedKinds (o : JsonObject) : Except String IntroducedKinds :=
  o.toArray.toList.mapM fun (kind, j) => do
    let k : JIntroducedKind ← (fromJson? j).mapError fun e =>
      s!"introducedKinds.{kind}: {e}"
    return (kind, k.arity)

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
  -- Stated exactly where a tuple can have a middle column, so the elaborator
  -- can say when one is about to be thrown away.
  match a.maxColumns.any (· ≤ 2), a.middleColumns with
  | false, none =>
    .error s!"an accepted form admitting more than two columns \
      ({a.minColumns}, {repr a.maxColumns}) does not say what becomes of the \
      middle ones"
  | true, some _ =>
    .error "an accepted form capped at two columns has no middle columns to declare"
  | _, _ => pure ()
  return { min := a.minColumns, max := a.maxColumns, requires := a.requires,
           middlesIgnored := a.middleColumns matches some .ignored }

private meta def altForm (a : JAltForm) : Except String RawAltForm := do
  unless a.type == "block" do .error "alternativeForm is not a block"
  let enums := a.fields.filterMap fun | .«enum» n => some n | _ => none
  let blocks := a.fields.filterMap fun | .block n b => some (n, b) | _ => none
  match enums with
  | [e] => return { enumField := e, blocks }
  | [] => .error "alternativeForm has no enum field"
  | _ => .error "two enum fields in alternativeForm"

private meta def fieldOf (kinds : IntroducedKinds) (itemId : String) (j : Json) :
    Except String (Option RawField) := do
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
  let introduces ← c.introduces.mapM fun i => do
    unless type matches RawFieldType.str do
      .error (here "a field introducing a graph-side name must be a string")
    let some arity := kinds.lookup i.kind
      | .error (here s!"introduces names the kind {i.kind.quote}, which \
          introducedKinds does not declare")
    return { field := name, arity, referencedBy := i.referencedBy }
  return some { name, type, required := c.required.getD false, alt, introduces }

/-- One manifest item to a `RawItem`: decode, drop it if deprecated, then lay
    its fields out as Lean arguments — positional order, the leading selector —
    and read the members that say what it introduces and what makes it inert. -/
private meta def itemOf (kinds : IntroducedKinds) (j : Json) :
    Except String (Option RawItem) := do
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
  let fields ← (i.fields.getD []).filterMapM (fieldOf kinds id)
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
  let introduces ← match fields.filterMap (·.introduces) with
    | [] => pure none
    | [i] => pure (some i)
    | is => .error (here s!"two fields introduce a name \
        ({", ".intercalate (is.map (·.field))}); an op introduces at most one")
  let effectFields := (i.inertWhenBare.map (·.effectFields)).getD []
  if i.inertWhenBare.isSome && effectFields.isEmpty then
    .error (here "inertWhenBare names no effect field, so every body would be inert")
  for f in effectFields do
    unless fields.any (·.name == f) do
      .error (here s!"inertWhenBare names the effect field {f.quote}, which it does not have")
  return some { id, yamlKey, constraint, scalar := shape matches .scalar,
                supportsHold := i.supportsHold.getD false,
                fields, positional, leadingSelector, introduces, effectFields,
                displaysSource := false }

private meta def blockOf (kinds : IntroducedKinds) (b : JBlock) :
    Except String RawBlock := do
  let fields ← b.fields.filterMapM (fieldOf kinds b.name)
  for f in fields do
    if f.required then
      .error s!"{b.name}.{f.name}: no representation for a required block field"
    if f.type.isBlock || f.alt.isSome then
      .error s!"{b.name}.{f.name}: blocks do not nest"
    if f.introduces.isSome then
      .error s!"{b.name}.{f.name}: a block leaf introduces no graph-side name"
  return { name := b.name, fields }

/-- Every id a field contributes: its own, plus the enum and block fields its
    alternative form spells. -/
private meta def RawField.ids (f : RawField) : List String :=
  f.name :: match f.alt with
    | some a => a.enumField :: a.blocks.map (·.1)
    | none => []

private meta def parseManifest : Except String RawManifest := do
  let json ← Json.parse manifestText
  -- Ahead of the record, so a manifest too old to carry a member says that
  -- rather than failing by the member's name.
  checkFormat (← member (Option String) json "manifestVersion")
  let m : JManifest ← fromJson? json
  let rawItems ← member (Array Json) json "items"
  let kinds ← introducedKinds m.introducedKinds

  -- The document section names are load-bearing for the lowering.
  unless m.document.sections matches [.constraints, .directives] do
    .error "document.sections moved; the lowering's section names are stale"

  let items ← rawItems.toList.filterMapM (itemOf kinds)
  let blocks ← m.blocks.mapM (blockOf kinds)
  let sourceFields ← m.source.fields.filterMapM (fieldOf kinds m.source.field)

  -- `Spec.lean`'s `OpSource` is these two fields, by name.
  unless sourceFields.map (·.name) == ["text", "location"] do
    .error s!"source.fields is {sourceFields.map (·.name)}; OpSource models \
      a text and a location"

  let mut deprecatedItems : List (String × String) := []
  let mut deprecatedFields : List (String × String) := []
  let mut fieldPaths : List String := []
  for j in rawItems do
    let i : JItem ← fromJson? j
    let fields ← (i.fields.getD []).mapM fun fj => (fromJson? fj : Except String JField)
    fieldPaths := fieldPaths ++ fields.map fun f => s!"{i.id}.{f.name}"
    match i.deprecated with
    | some d => deprecatedItems := deprecatedItems ++ [(i.id, d.replacedBy)]
    | none =>
      for f in fields do
        if let some d := f.deprecated then
          deprecatedFields := deprecatedFields ++ [(s!"{i.id}.{f.name}", d.replacedBy)]

  -- A reference site is a position in the manifest's own surface, deprecated
  -- ones included: it says where the engine resolves the name, not where this
  -- package writes it.
  for i in items do
    if let some intro := i.introduces then
      for path in intro.referencedBy do
        unless fieldPaths.contains path do
          .error s!"{i.id}.{intro.field}: introduces.referencedBy names \
            {path.quote}, which is not a field"

  -- Verify the house-style tables still name live manifest entries.
  for id in leadingSelectorOverride do
    unless items.any (·.id == id) do
      .error s!"house style: a table names {id.quote}, which is not a live item"
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
      .error s!"house style: boolSugar {word.quote} names the field {fname.quote}, \
        which no live item has"

  -- Hold support is stated twice, per item and as one list, so each side
  -- checks the other. `supportedBy` may also name a deprecated item, which the
  -- liveness check above allows and this loop does not see.
  for i in items do
    let listed := m.hold.supportedBy.contains i.id
    unless i.supportsHold == listed do
      .error s!"{i.id}: items[].supportsHold is {i.supportsHold} but \
        hold.supportedBy {if listed then "lists" else "does not list"} it"

  -- An absent `inertWhenBare` is indistinguishable from "not inert", so the
  -- member going away would take the bare-body check with it silently.
  unless items.any fun i => !i.effectFields.isEmpty do
    .error "no item declares inertWhenBare; the member left the manifest or \
      the pin moved past it"

  let items := items.map fun i =>
    { i with displaysSource := m.source.displayedBy.contains i.id }

  -- Field ids are global across items, blocks and the source stamp: the same
  -- name means the same serialized key everywhere.
  let fieldIds := ((items.flatMap (·.fields) ++ blocks.flatMap (·.fields)
    ++ sourceFields).flatMap RawField.ids).eraseDups
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
  /-- The engine keeps only the first and last column of a tuple this wide
      (`middleColumns`); `inferredEdge` and `tag` are the positions that
      instead show them. -/
  middlesIgnored : Bool
  deriving Repr, Inhabited

/-- A graph-side name an op introduces: the string field that spells it, how
    many columns the thing it names has, and the `item.field` positions where
    the engine resolves such a name. A reference from anywhere else is never
    looked up — selectors evaluate against the data instance, and the field
    positions that are not listed match before the name exists. -/
public meta structure Introduces where
  field : FieldId
  arity : Nat
  referencedBy : List String
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
  /-- The graph-side name this op introduces, for later ops in the same spec
      to reference. -/
  introduces : Option Introduces
  /-- The fields that are this item's entire effect (`inertWhenBare`): an
      instance setting none of them parses and does nothing, which elaboration
      rejects. Empty for an item that is not inert when bare. -/
  effectFields : List FieldId
  /-- Core reads this op's `source` stamp back out, so carrying one buys a
      conflict report that quotes the author. Elsewhere it parses and is
      ignored, and the stamp is left off. -/
  displaysSource : Bool
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
`hold.supportedBy`. `sourceField` is the key the provenance stamp rides under,
likewise item-level as `ItemSpec.displaysSource`. `boolSugar` is the bare words
above, resolved to field ids. `deprecatedItems` and `deprecatedFields` are the
account of the surface we decline, so a coverage test can insist nothing is
dropped silently. -/

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

private meta def declareDef (name : Name) (ty val : Term) : CommandElabM Unit := do
  elabCommand (← `(public meta def $(mkIdent name):ident : $ty := $val))

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

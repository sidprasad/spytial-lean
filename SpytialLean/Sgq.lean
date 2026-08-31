module

public import Lean
public meta import SpytialLean.ManifestJson

namespace SpytialLean.Sgq

open Lean Elab Command SpytialLean.ManifestJson

/-! # The SGQ language, read off its manifest

simple-graph-query publishes its grammar as `docs/sgq-language.json`; this module
parses the resolved package's copy into id enumerations and tables. -/

-- TODO(sgq#68): unpublished; pnpm-workspace.yaml overrides the package to a
-- local checkout until a release ships the manifest.
private meta def manifestText : String :=
  include_str ".." / "node_modules" / "simple-graph-query" / "docs" / "sgq-language.json"

private meta def alternativeRoles : List String := ["product.multiplicity"]

/-- Keyed by op id or `construct.role`; the default is grammar order's first. -/
private meta def preferredSpelling : List (String × String) :=
  [ ("or", "or"), ("and", "and"), ("not", "not"), ("iff", "iff"),
    ("implies", "implies"), ("atMost", "<="),
    -- what the selector reference documents
    ("comparison.negation", "!") ]

/-! ## The language as data -/

json_union Kind where
  | relation
  | number
  | boolean
  | «string»
  | operand
  | any

deriving instance DecidableEq for Kind

/-- `none` is the manifest's `null`: the construct does not settle the kind, so
    read its operators — or, for `f[a]`, the callee. -/
public meta structure Kinds where
  yields : Option Kind
  operands : List (Option Kind)
  inner : Option Kind
  deriving Repr, Inhabited, FromJson

/-- The coarse classification; `template` is where the pieces actually go. -/
json_union Fixity where
  | «infix»
  | «prefix»
  | atom
  | bracket
  | binder
  | quantifier
  | comprehension

deriving instance DecidableEq for Fixity

/-- `slot` is as wide as that operand, `sum` the two added, `join` is
    `a + b - 2`, `boxJoin` folds `join` over an argument list. -/
json_union ArityRule on "rule" where
  | slot (index : Nat)
  | fixed (width : Nat)
  | «sum»
  | «join»
  | boxJoin
  | binders

json_union Requires where
  | equal

public meta structure Arity where
  yields : Option ArityRule
  slots : List (Option Nat)
  requires : Option Requires
  deriving Repr, Inhabited, FromJson

public meta structure Range where
  «from» : Char
  to : Char
  deriving Repr, Inhabited, FromJson

public meta structure CharClass where
  ranges : List Range
  chars : List Char
  deriving Repr, Inhabited, FromJson

public meta def CharClass.contains (cc : CharClass) (c : Char) : Bool :=
  cc.ranges.any (fun r => r.from ≤ c && c ≤ r.to) || cc.chars.contains c

public meta structure Part where
  /-- One of `spellings`; this package's choice. -/
  text : String
  spellings : List String
  /-- Alternatives at each use, not aliases: an encoder writes `text` for an
      alias and the source's own spelling for an alternative. -/
  alternatives : Bool
  deriving Repr, Inhabited

public meta def loosest : Nat := 0

/-! ## The manifest as records

Roles and ids stay strings until the enumerations exist. -/

json_union BinderStyle where
  | typed
  | bound

json_union JItem on "item" where
  | operand (level : Nat)
  | «repeat» (level : Nat)
  | list (level : Nat) (role : String)
  | binders (style : BinderStyle) (level : Nat)
  | body (level : Nat)
  | name (qualified : Bool)
  | constant
  | operator
  | part (role : String) («optional» : Bool)
  | «optional» (items : List JItem)

/-- A binder group and a body carry no role of their own. -/
private meta partial def JItem.roles : JItem → List String
  | .list _ r => [r]
  | .part r _ => [r]
  | .binders style _ => ["separator", if style matches .typed then "colon" else "bind"]
  | .body _ => ["bar"]
  | .«optional» is => is.flatMap JItem.roles
  | _ => []

public meta structure JOp where
  id : String
  spellings : List String
  evaluates : Bool
  kinds : Kinds
  arity : Arity
  deriving Inhabited, FromJson

public meta structure JConstruct where
  id : String
  precedence : Nat
  fixity : Fixity
  evaluates : Bool
  kinds : Kinds
  arity : Arity
  template : List JItem
  /-- Keys are data, so this stays an object rather than becoming a record. -/
  parts : JsonObject
  operators : List JOp
  deriving Inhabited, FromJson

public meta structure JQuoted where
  delimiter : Char
  escape : Char
  mustEscape : List Char
  escapeDecodes : JsonObject
  minLength : Nat
  deriving Inhabited, FromJson

public meta structure JBare where
  head : CharClass
  rest : CharClass
  minLength : Nat
  deriving Inhabited, FromJson

public meta structure JIdentifier where
  bare : JBare
  quoted : JQuoted
  /-- Spellings a bare identifier cannot carry: they lex as some other token. -/
  reserved : List String
  deriving Inhabited, FromJson

public meta structure JBuiltins where
  binary : List String
  unary : List String
  set : List String
  deriving Inhabited, FromJson

public meta structure JManifest where
  sgqVersion : String
  identifier : JIdentifier
  «string» : JQuoted
  builtins : JBuiltins
  deriving Inhabited, FromJson

/-! ## Assembling the tables' input -/

private meta structure RawOp where
  id : String
  construct : String
  text : String
  spellings : List String
  evaluates : Bool
  kinds : Kinds
  arity : Arity

private meta structure RawConstruct where
  id : String
  prec : Nat
  fixity : Fixity
  evaluates : Bool
  kinds : Kinds
  arity : Arity
  template : List JItem
  parts : List (String × Part)
  operators : List String

private meta structure RawManifest where
  lexical : JManifest
  constructs : List RawConstruct
  ops : List RawOp
  roles : List String
  lexemes : List String
  stringEscapes : List (Char × Char)

private meta def pick (what : String) (spellings : List String) : Except String String :=
  match preferredSpelling.lookup what with
  | some s =>
    if spellings.contains s then .ok s
    else .error s!"{what}: preferred spelling {s.quote} is no longer one of {spellings}"
  | none =>
    match spellings with
    | s :: _ => .ok s
    | [] => .error s!"{what}: has no spelling"

private meta def escapePairs (o : JsonObject) : Except String (List (Char × Char)) :=
  o.toArray.toList.mapM fun (spelling, decoded) => do
    let decoded : Char ← (fromJson? decoded).mapError fun e =>
      s!"string.escapeDecodes.{spelling}: {e}"
    let spelling : Char ← (fromJson? (Json.str spelling)).mapError fun e =>
      s!"string.escapeDecodes: {e}"
    return (decoded, spelling)

/-- Lean's lexer claims a numeric literal before any token table does, so
    `constant` has no generated rule and `SelectorElab.sgqNegNumRule` writes the
    sign itself. -/
private meta def namedParts : List (String × String) := [("constant", "negation")]

private meta def parseManifest : Except String RawManifest := do
  let json ← Json.parse manifestText
  let m : JManifest ← fromJson? json
  let constructs ← eachKeyedBy JConstruct "id" (← member (Array Json) json "constructs")

  let escapes := m.identifier.quoted.escapeDecodes.toArray.map (·.1)
  unless escapes.isEmpty do
    .error s!"identifier.quoted now decodes the escapes \
      {", ".intercalate (escapes.toList.map (·.quote))}; Selector.lean assumes a \
      backslash only removes itself"

  let mut cons : List RawConstruct := []
  let mut ops : List RawOp := []
  let mut lexemes : List String := []
  for c in constructs do
    let mut parts : List (String × Part) := []
    for (role, raw) in c.parts.toArray do
      let spellings : List String ← (fromJson? raw).mapError fun e =>
        s!"{c.id}.parts.{role}: {e}"
      lexemes := lexemes ++ spellings
      parts := parts ++ [(role, {
        text := ← pick s!"{c.id}.{role}" spellings,
        spellings := spellings,
        alternatives := alternativeRoles.contains s!"{c.id}.{role}" })]
    for role in c.template.flatMap JItem.roles do
      unless parts.any (·.1 == role) do
        .error s!"{c.id}: the template is written with the part {role.quote}, \
          which it has no spelling for"
    for o in c.operators do
      lexemes := lexemes ++ o.spellings
      ops := ops ++ [{
        id := o.id, construct := c.id,
        text := ← pick o.id o.spellings, spellings := o.spellings,
        evaluates := o.evaluates, kinds := o.kinds, arity := o.arity }]
    cons := cons ++ [{
      id := c.id, prec := c.precedence, fixity := c.fixity,
      evaluates := c.evaluates, kinds := c.kinds, arity := c.arity,
      template := c.template, parts,
      operators := c.operators.map (·.id) }]

  for (cid, role) in namedParts do
    let some c := cons.find? (·.id == cid)
      | .error s!"namedParts names {cid.quote}, which is not a live construct"
    unless c.parts.any (·.1 == role) do
      .error s!"{cid}: the package writes the part {role.quote}, which it has \
        no spelling for"

  let dup := ops.filter fun o => 1 < (ops.filter (·.id == o.id)).length
  unless dup.isEmpty do
    .error s!"operator ids are not unique: {dup.map (·.id)}"

  return {
    lexical := m, constructs := cons, ops,
    roles := (cons.flatMap fun c => c.parts.map (·.1)).eraseDups,
    lexemes := lexemes.eraseDups,
    stringEscapes := ← escapePairs m.string.escapeDecodes }

private meta def manifest! : CommandElabM RawManifest := do
  match parseManifest with
  | .ok m => return m
  | .error e => throwError "sgq manifest: {e}"

private meta def enumCtor (enum : Name) (id : String) : Ident :=
  mkIdent (`SpytialLean.Sgq ++ enum ++ Name.mkSimple id)

private meta def declareEnum (enum : Name) (all : Name) (ids : List String) :
    CommandElabM Unit := do
  let ctors ← ids.mapM fun s =>
    `(Lean.Parser.Command.ctor| | $(mkIdent (Name.mkSimple s)):ident)
  elabCommand (← `(public meta inductive $(mkIdent enum):ident where
      $(ctors.toArray)*
      deriving Repr, DecidableEq, Inhabited, Hashable))
  let refs := (ids.map (enumCtor enum)).toArray
  elabCommand (← `(public meta def $(mkIdent all):ident :
      List $(mkIdent enum):ident := [$refs,*]))

elab "derive_sgq_ids" : command => do
  let m ← manifest!
  declareEnum `ConstructId `allConstructs (m.constructs.map (·.id))
  declareEnum `OpId `allOps (m.ops.map (·.id))
  declareEnum `Role `allRoles m.roles

derive_sgq_ids

/-! ## The enum-carrying vocabulary -/

/-- One position in a production, in source order. `level` is the cascade level
    that position descends to, which is not always the neighbouring one. -/
public meta inductive Item where
  | operand (level : Nat)
  | «repeat» (level : Nat)
  | list (level : Nat) (role : Role)
  /-- `x, y : dom` when `typed`, `x = e` when not. -/
  | binders (typed : Bool) (level : Nat)
  | body (level : Nat)
  | name (qualified : Bool)
  /-- The `const` alternation; the numeric and string literals it also spells
      are `Sel` leaves of their own. -/
  | constant
  | operator
  | part (role : Role) (optional : Bool)
  | «optional» (items : List Item)
  deriving Inhabited

public meta structure Op where
  id : OpId
  name : String
  construct : ConstructId
  text : String
  spellings : List String
  evaluates : Bool
  kinds : Kinds
  arity : Arity
  deriving Repr, Inhabited

public meta structure Construct where
  id : ConstructId
  name : String
  prec : Nat
  fixity : Fixity
  evaluates : Bool
  kinds : Kinds
  arity : Arity
  template : List Item
  parts : List (Role × Part)
  operators : List OpId
  deriving Inhabited

/-! ## The tables -/

private meta instance : Quote Kind := ⟨fun
  | .relation => mkCIdent ``Kind.relation
  | .number => mkCIdent ``Kind.number
  | .boolean => mkCIdent ``Kind.boolean
  | .«string» => mkCIdent ``Kind.«string»
  | .operand => mkCIdent ``Kind.operand
  | .any => mkCIdent ``Kind.any⟩

private meta instance : Quote Kinds := ⟨fun k =>
  Syntax.mkCApp ``Kinds.mk #[quote k.yields, quote k.operands, quote k.inner]⟩

private meta instance : Quote ArityRule := ⟨fun
  | .fixed n => Syntax.mkCApp ``ArityRule.fixed #[quote n]
  | .slot i => Syntax.mkCApp ``ArityRule.slot #[quote i]
  | .«sum» => mkCIdent ``ArityRule.«sum»
  | .«join» => mkCIdent ``ArityRule.«join»
  | .boxJoin => mkCIdent ``ArityRule.boxJoin
  | .binders => mkCIdent ``ArityRule.binders⟩

private meta instance : Quote Requires := ⟨fun
  | .equal => mkCIdent ``Requires.equal⟩

private meta instance : Quote Arity := ⟨fun a =>
  Syntax.mkCApp ``Arity.mk #[quote a.yields, quote a.slots, quote a.requires]⟩

private meta instance : Quote Fixity := ⟨fun
  | .«infix» => mkCIdent ``Fixity.«infix»
  | .«prefix» => mkCIdent ``Fixity.«prefix»
  | .atom => mkCIdent ``Fixity.atom
  | .bracket => mkCIdent ``Fixity.bracket
  | .binder => mkCIdent ``Fixity.binder
  | .quantifier => mkCIdent ``Fixity.quantifier
  | .comprehension => mkCIdent ``Fixity.comprehension⟩

private meta instance : Quote Part := ⟨fun p =>
  Syntax.mkCApp ``Part.mk #[quote p.text, quote p.spellings, quote p.alternatives]⟩

private meta instance : Quote Char := ⟨fun c =>
  Syntax.mkCApp ``Char.ofNat #[quote c.toNat]⟩

private meta instance : Quote Range := ⟨fun r =>
  Syntax.mkCApp ``Range.mk #[quote r.from, quote r.to]⟩

private meta instance : Quote CharClass := ⟨fun cc =>
  Syntax.mkCApp ``CharClass.mk #[quote cc.ranges, quote cc.chars]⟩

-- `quote (List Term)` splices pre-built terms verbatim
private meta instance : Quote Term := ⟨id⟩

private meta partial def quoteItem : JItem → Term
  | .operand l => Syntax.mkCApp ``Item.operand #[quote l]
  | .«repeat» l => Syntax.mkCApp ``Item.«repeat» #[quote l]
  | .list l r => Syntax.mkCApp ``Item.list #[quote l, enumCtor `Role r]
  | .binders s l => Syntax.mkCApp ``Item.binders #[quote (s matches .typed), quote l]
  | .body l => Syntax.mkCApp ``Item.body #[quote l]
  | .name q => Syntax.mkCApp ``Item.name #[quote q]
  | .constant => mkCIdent ``Item.constant
  | .operator => mkCIdent ``Item.operator
  | .part r o => Syntax.mkCApp ``Item.part #[enumCtor `Role r, quote o]
  | .«optional» is =>
    Syntax.mkCApp ``Item.«optional» #[quote (is.map quoteItem)]

private meta def quoteOp (o : RawOp) : Term :=
  Syntax.mkCApp ``Op.mk #[enumCtor `OpId o.id, quote o.id, enumCtor `ConstructId o.construct,
    quote o.text, quote o.spellings, quote o.evaluates, quote o.kinds, quote o.arity]

private meta def quoteConstruct (c : RawConstruct) : Term :=
  let parts := c.parts.map fun (role, part) =>
    Syntax.mkCApp ``Prod.mk #[enumCtor `Role role, quote part]
  Syntax.mkCApp ``Construct.mk #[enumCtor `ConstructId c.id, quote c.id, quote c.prec,
    quote c.fixity, quote c.evaluates, quote c.kinds, quote c.arity,
    quote (c.template.map quoteItem), quote parts,
    quote (c.operators.map fun o => (enumCtor `OpId o : Term))]

private meta def declareDef (name : Name) (ty val : Term) : CommandElabM Unit := do
  elabCommand (← `(public meta def $(mkIdent name):ident : $ty := $val))

elab "derive_sgq_tables" : command => do
  let m ← manifest!
  declareDef `ops (← `(Array Op)) (← `(#[$((m.ops.map quoteOp).toArray),*]))
  declareDef `constructs (← `(Array Construct))
    (← `(#[$((m.constructs.map quoteConstruct).toArray),*]))
  declareDef `lexemes (← `(List String)) (quote m.lexemes)
  declareDef `reserved (← `(List String)) (quote m.lexical.identifier.reserved)
  declareDef `bareHeadClass (← `(CharClass)) (quote m.lexical.identifier.bare.head)
  declareDef `bareRestClass (← `(CharClass)) (quote m.lexical.identifier.bare.rest)
  declareDef `bareMinLength (← `(Nat)) (quote m.lexical.identifier.bare.minLength)
  declareDef `quoteDelimiter (← `(Char)) (quote m.lexical.identifier.quoted.delimiter)
  declareDef `quoteEscape (← `(Char)) (quote m.lexical.identifier.quoted.escape)
  declareDef `quoteMustEscape (← `(List Char)) (quote m.lexical.identifier.quoted.mustEscape)
  declareDef `quoteMinLength (← `(Nat)) (quote m.lexical.identifier.quoted.minLength)
  declareDef `stringDelimiter (← `(Char)) (quote m.lexical.string.delimiter)
  declareDef `stringEscape (← `(Char)) (quote m.lexical.string.escape)
  declareDef `stringMustEscape (← `(List Char)) (quote m.lexical.string.mustEscape)
  declareDef `stringEscapes (← `(List (Char × Char))) (quote m.stringEscapes)
  declareDef `binaryBuiltins (← `(List String)) (quote m.lexical.builtins.binary)
  declareDef `unaryBuiltins (← `(List String)) (quote m.lexical.builtins.unary)
  declareDef `setBuiltins (← `(List String)) (quote m.lexical.builtins.set)

derive_sgq_tables

public meta def Op.of (o : OpId) : Op :=
  (ops.find? (·.id == o)).getD default

public meta def Construct.of (c : ConstructId) : Construct :=
  (constructs.find? (·.id == c)).getD default

public meta def constructName (c : ConstructId) : String := (Construct.of c).name

public meta def opName (o : OpId) : String := (Op.of o).name

/-- Total for the roles this package reads: the derive command checks that every
    part a template or `namedParts` names has a spelling. -/
public meta def Construct.part (c : Construct) (r : Role) : Part :=
  (c.parts.lookup r).getD { text := "", spellings := [], alternatives := false }

public meta def Op.prec (o : Op) : Nat := (Construct.of o.construct).prec

/-- Spellings are unique within a construct, so at most one operator matches. -/
public meta def Construct.operatorSpelled (c : Construct) (s : String) : Option OpId :=
  c.operators.find? fun o => (Op.of o).spellings.contains s

public meta def Construct.spellings (c : Construct) : List String :=
  c.operators.flatMap fun o => (Op.of o).spellings

public meta def bareHead (c : Char) : Bool := bareHeadClass.contains c

public meta def bareRest (c : Char) : Bool := bareRestClass.contains c

/-- The engine resolves these; anything else after the escape denotes itself. -/
public meta def stringEscapeSpelling (c : Char) : Option Char :=
  stringEscapes.lookup c

end SpytialLean.Sgq

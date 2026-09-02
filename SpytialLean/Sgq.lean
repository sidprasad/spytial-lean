module

public import Lean
public meta import SpytialLean.ManifestJson

namespace SpytialLean.Sgq

open Lean Elab Command SpytialLean.ManifestJson

/-! # The SGQ language, read off its manifest

simple-graph-query publishes its grammar as `docs/sgq-language.json`; this module
parses the resolved package's copy into id enumerations and tables. -/

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
  deriving Repr, Inhabited

json_record Kinds

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

/-- The static analyzer's rule; the evaluator re-checks it only for `++`. -/
json_union Requires where
  | equal

public meta structure Arity where
  yields : Option ArityRule
  slots : List (Option Nat)
  requires : Option Requires
  deriving Repr, Inhabited

json_record Arity

public meta structure Range where
  «from» : Char
  to : Char
  deriving Repr, Inhabited

json_record Range

public meta structure CharClass where
  ranges : List Range
  chars : List Char
  deriving Repr, Inhabited

json_record CharClass

public meta def CharClass.contains (cc : CharClass) (c : Char) : Bool :=
  cc.ranges.any (fun r => r.from ≤ c && c ≤ r.to) || cc.chars.contains c

public meta structure Part where
  /-- The spelling this package writes. One of `spellings`; its choice. -/
  text : String
  /-- Every spelling the engine accepts, in grammar order. -/
  spellings : List String
  /-- Whether the spellings are alternatives to choose between at each use
      (an arrow's multiplicity) rather than aliases for one thing (`!` and
      `not`). An encoder writes `text` for an alias and what the source
      wrote for an alternative. -/
  alternatives : Bool
  deriving Repr, Inhabited

/-- The level of the loosest expression: what a delimiter accepts inside it. -/
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

/-- The parts an item is written with. A binder group and a body carry no role
    of their own, so the two readers of a template (`SelectorElab`'s rules and
    `Selector`'s lowering) reach for theirs by name. -/
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
  deriving Inhabited

json_record JOp

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
  deriving Inhabited

-- the template's cascade levels already encode associativity
json_record JConstruct ignoring "associativity"

public meta structure JQuoted where
  delimiter : Char
  escape : Char
  mustEscape : List Char
  escapeDecodes : JsonObject
  minLength : Nat
  deriving Inhabited

json_record JQuoted

public meta structure JBare where
  head : CharClass
  rest : CharClass
  minLength : Nat
  deriving Inhabited

json_record JBare

public meta structure JIdentifier where
  bare : JBare
  quoted : JQuoted
  /-- Spellings a bare identifier cannot carry: they lex as some other token. -/
  reserved : List String
  deriving Inhabited

json_record JIdentifier

public meta structure JBuiltins where
  binary : List String
  unary : List String
  set : List String
  deriving Inhabited

json_record JBuiltins

public meta structure JManifest where
  sgqVersion : String
  identifier : JIdentifier
  «string» : JQuoted
  builtins : JBuiltins
  deriving Inhabited

-- `constructs` is read on its own; `number` describes numerals Lean's lexer claims
json_record JManifest ignoring "constructs" "number"

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

/-- Parts reached by construct and role rather than off a template item, which
    is the one way a template walk cannot see them. Lean's lexer claims a
    numeric literal before any token table does, so `constant` has no generated
    rule and `SelectorElab.sgqNegNumRule` writes the sign itself. -/
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

  let cons : List RawConstruct ← constructs.toList.mapM fun c => do
    let parts : List (String × Part) ← c.parts.toArray.toList.mapM fun (role, raw) => do
      let spellings : List String ← (fromJson? raw).mapError fun e =>
        s!"{c.id}.parts.{role}: {e}"
      return (role, {
        text := ← pick s!"{c.id}.{role}" spellings, spellings,
        alternatives := alternativeRoles.contains s!"{c.id}.{role}" })
    for role in c.template.flatMap JItem.roles do
      unless parts.any (·.1 == role) do
        .error s!"{c.id}: the template is written with the part {role.quote}, \
          which it has no spelling for"
    for item in c.template do
      if let .«optional» inner := item then
        unless inner.all (fun i => i matches .operand _ | .part ..) do
          .error s!"{c.id}: an optional template group may hold only operands \
            and parts; the elaborator reads nothing else inside one"
    return { id := c.id, prec := c.precedence, fixity := c.fixity,
             evaluates := c.evaluates, kinds := c.kinds, arity := c.arity,
             template := c.template, parts,
             operators := c.operators.map (·.id) }
  let ops := (← constructs.toList.mapM fun c => c.operators.mapM fun o => do
    return ({ id := o.id, construct := c.id,
              text := ← pick o.id o.spellings, spellings := o.spellings,
              evaluates := o.evaluates, kinds := o.kinds,
              arity := o.arity } : RawOp)).flatten
  let lexemes := cons.flatMap (fun c => c.parts.flatMap (·.2.spellings))
    ++ ops.flatMap (·.spellings)

  let partKeys := cons.flatMap fun c => c.parts.map fun (role, _) => s!"{c.id}.{role}"
  for (key, _) in preferredSpelling do
    unless ops.any (·.id == key) || partKeys.contains key do
      .error s!"preferredSpelling names {key.quote}, which is neither a live \
        operator nor a construct part"
  for key in alternativeRoles do
    unless partKeys.contains key do
      .error s!"alternativeRoles names {key.quote}, which is not a construct part"

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

private meta def manifest! : CommandElabM RawManifest :=
  ManifestJson.manifest! "sgq manifest" parseManifest

private meta def enumCtor : Name → String → Ident :=
  ManifestJson.enumCtor `SpytialLean.Sgq

elab "derive_sgq_ids" : command => do
  let m ← manifest!
  let constructIds := m.constructs.map (·.id)
  let opIds := m.ops.map (·.id)
  declareEnum `ConstructId constructIds
  declareEnum `OpId opIds
  declareEnum `Role m.roles
  declareAll `allConstructs `ConstructId constructIds
  declareAll `allOps `OpId opIds
  declareAll `allRoles `Role m.roles
  declareNames `constructName `ConstructId constructIds
  declareNames `opName `OpId opIds

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
  construct : ConstructId
  text : String
  spellings : List String
  evaluates : Bool
  kinds : Kinds
  arity : Arity
  deriving Repr, Inhabited

public meta structure Construct where
  id : ConstructId
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

private meta instance : Quote Range := ⟨fun r =>
  Syntax.mkCApp ``Range.mk #[quote r.from, quote r.to]⟩

private meta instance : Quote CharClass := ⟨fun cc =>
  Syntax.mkCApp ``CharClass.mk #[quote cc.ranges, quote cc.chars]⟩

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
  Syntax.mkCApp ``Op.mk #[enumCtor `OpId o.id, enumCtor `ConstructId o.construct,
    quote o.text, quote o.spellings, quote o.evaluates, quote o.kinds, quote o.arity]

private meta def quoteConstruct (c : RawConstruct) : Term :=
  let parts := c.parts.map fun (role, part) =>
    Syntax.mkCApp ``Prod.mk #[enumCtor `Role role, quote part]
  Syntax.mkCApp ``Construct.mk #[enumCtor `ConstructId c.id, quote c.prec,
    quote c.fixity, quote c.evaluates, quote c.kinds, quote c.arity,
    quote (c.template.map quoteItem), quote parts,
    quote (c.operators.map fun o => (enumCtor `OpId o : Term))]

private meta def declareDef (name : Name) (ty val : Term) : CommandElabM Unit := do
  elabCommand (← `(public meta def $(mkIdent name):ident : $ty := $val))

elab "derive_sgq_tables" : command => do
  let m ← manifest!
  declareTable `Op.of `OpId (← `(Op)) (m.ops.map fun o => (o.id, quoteOp o))
  declareTable `Construct.of `ConstructId (← `(Construct))
    (m.constructs.map fun c => (c.id, quoteConstruct c))
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

/-- Total for the roles this package reads: the derive command checks that every
    part a template or `namedParts` names has a spelling. -/
public meta def Construct.part (c : Construct) (r : Role) : Part :=
  (c.parts.lookup r).getD { text := "", spellings := [], alternatives := false }

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

module

public import Lean
public meta import SpytialLean.ManifestJson

namespace SpytialLean.Sgq

open Lean Elab Command SpytialLean.ManifestJson

/-! # The SGQ language, read off its manifest at elaboration time

simple-graph-query publishes its grammar as `docs/sgq-language.json`; the
commands below parse the resolved package's copy while this module elaborates
and declare the id enumerations and tables. The parser, the elaborator and
the lowering read these and name no construct, so a construct added upstream
arrives by rebuilding against the bumped dependency.

A fixity, kind, template item, arity rule or part role with no representation
here stops elaboration naming the construct, rather than yielding a plausible
table. -/

-- The resolved package's manifest. Missing ⇒ this module does not elaborate;
-- until a release ships it, pnpm-workspace.yaml overrides the package to a
-- local checkout.
private meta def manifestText : String :=
  include_str ".." / "node_modules" / "simple-graph-query" / "docs" / "sgq-language.json"

/-! ## Which spelling spytial-lean writes

A token can have aliases (`or` is also `||`). The manifest lists them in
grammar order and takes no view; which one to *emit* is this package's house
style. -/

/-- Roles whose several spellings are alternatives to choose between at each
    use (an arrow's multiplicity), not aliases for one thing. -/
private meta def alternativeRoles : List String := ["product.multiplicity"]

/-- Overrides for what to *emit* where the engine accepts several spellings.
    Without an entry the first in grammar order wins, so a new alias upstream
    is a no-op unless it is inserted ahead of the one we already write — and
    then the lowering goldens catch it. -/
private meta def preferredSpelling : List (String × String) :=
  [ ("or", "or"), ("and", "and"), ("not", "not"), ("iff", "iff"),
    ("implies", "implies"), ("atMost", "<="),
    -- `!in` / `!ni` / `!=` read better than the `not` prefix, and are what the
    -- selector reference documents.
    ("comparison.negation", "!") ]

/-! ## The language as data -/

json_union Kind where
  | "relation" => relation
  | "number" => number
  | "boolean" => boolean
  | "string" => «string»
  | "operand" => operand
  | "any" => any

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
  | "infix" => «infix»
  | "prefix" => «prefix»
  | "atom" => atom
  | "bracket" => bracket
  | "binder" => binder
  | "quantifier" => quantifier
  | "comprehension" => comprehension

deriving instance DecidableEq for Fixity

/-- `slot` is as wide as that operand, `sum` the two added, `join` is
    `a + b - 2`, `boxJoin` folds `join` over an argument list. -/
json_union ArityRule on "rule" where
  | "slot" => slot (index : Nat)
  | "fixed" => fixed (width : Nat)
  | "sum" => «sum»
  | "join" => «join»
  | "boxJoin" => boxJoin
  | "binders" => binders

/-- The static analyzer's rule; the evaluator re-checks it only for `++`. -/
json_union Requires where
  | "equal" => equal

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
  /-- The spelling this package writes. One of `spellings`; house style. -/
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
  | "typed" => typed
  | "bound" => bound

json_union JItem on "item" where
  | "operand" => operand (level : Nat)
  | "repeat" => «repeat» (level : Nat)
  | "list" => list (level : Nat) (role : String)
  | "binders" => binders (style : BinderStyle) (level : Nat)
  | "body" => body (level : Nat)
  | "name" => name (qualified : Bool)
  | "constant" => constant
  | "operator" => operator
  | "part" => part (role : String) («optional» : Bool)
  | "optional" => «optional» (items : List JItem)

private meta partial def JItem.roles : JItem → List String
  | .list _ r => [r]
  | .part r _ => [r]
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

private meta def parseManifest : Except String RawManifest := do
  let json ← Json.parse manifestText
  let m : JManifest ← fromJson? json
  let constructs ← eachKeyedBy JConstruct "id" (← member (Array Json) json "constructs")

  unless (m.identifier.quoted.escapeDecodes.getJson? "n").isNone do
    .error "identifier.quoted now decodes escapes; Selector.lean assumes a \
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
    -- a template naming a role the construct has no spelling for would look
    -- up nothing at every use; catch it here instead
    for role in c.template.flatMap JItem.roles do
      unless parts.any (·.1 == role) do
        .error s!"{c.id}: the template names the part {role.quote}, which it \
          has no spelling for"
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

/-! ## The id enumerations

Construct, operator and part-role ids as generated enumerations, so a table
lookup is total and a misspelling is a type error. -/

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

/-- One position in a production, in source order.

    `level` is the cascade level that position descends to. A subexpression
    needs parentheses exactly when its own precedence is below the level of
    the slot it fills — which is not always the neighbouring level, so these
    are read rather than assumed. -/
public meta inductive Item where
  /-- A subexpression. -/
  | operand (level : Nat)
  /-- Zero or more subexpressions, whitespace-separated. -/
  | «repeat» (level : Nat)
  /-- A separated argument list. -/
  | list (level : Nat) (role : Role)
  /-- Binder groups: `x, y : dom` when `typed`, `x = e` when not. -/
  | binders (typed : Bool) (level : Nat)
  /-- The bar and the body of a binder or a comprehension. -/
  | body (level : Nat)
  /-- A bare name. -/
  | name (qualified : Bool)
  /-- The `const` alternation: a named constant, or a numeric or string
      literal, whose spelling the lexical sections carry. -/
  | constant
  /-- Which operator was written. -/
  | operator
  | part (role : Role) (optional : Bool)
  /-- A group taken as a whole or not at all (`implies … else …`). -/
  | «optional» (items : List Item)
  deriving Inhabited

public meta structure Op where
  id : OpId
  /-- The manifest's own spelling of the id, for diagnostics. -/
  name : String
  construct : ConstructId
  /-- The spelling this package writes. One of `spellings`; house style. -/
  text : String
  spellings : List String
  /-- Whether the engine runs this operator: `is` parses and is refused
      while every other comparison evaluates. -/
  evaluates : Bool
  kinds : Kinds
  arity : Arity
  deriving Repr, Inhabited

/-- The cascade levels a construct's operands descend to live in its
    `template`, which is what the parser and the encoder read; they are not
    repeated here. -/
public meta structure Construct where
  id : ConstructId
  /-- The manifest's own spelling of the id: node kinds and diagnostics. -/
  name : String
  prec : Nat
  fixity : Fixity
  /-- Whether the engine runs the construct or parses it and refuses. -/
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

/-! ## Reading the tables -/

public meta def Op.of (o : OpId) : Op :=
  (ops.find? (·.id == o)).getD default

public meta def Construct.of (c : ConstructId) : Construct :=
  (constructs.find? (·.id == c)).getD default

/-- The manifest's own spelling of the id, for node kinds and diagnostics. -/
public meta def constructName (c : ConstructId) : String := (Construct.of c).name

public meta def opName (o : OpId) : String := (Op.of o).name

/-- A role the construct spells. Total by construction: the derive command
    checks that every role a template names is one the construct has. -/
public meta def Construct.part (c : Construct) (r : Role) : Part :=
  (c.parts.lookup r).getD { text := "", spellings := [], alternatives := false }

public meta def Op.prec (o : Op) : Nat := (Construct.of o.construct).prec

/-- The operator of `c` written as `s`, if any. Spellings are unique within a
    construct, so this is a function of the atom the parser captured. -/
public meta def Construct.operatorSpelled (c : Construct) (s : String) : Option OpId :=
  c.operators.find? fun o => (Op.of o).spellings.contains s

/-- Every spelling of any of `c`'s operators, in grammar order. -/
public meta def Construct.spellings (c : Construct) : List String :=
  c.operators.flatMap fun o => (Op.of o).spellings

/-! ## Names and literals -/

/-- Spellings a bare identifier cannot carry: they lex as some other token.
    (`reserved`, declared above, is the list itself.) -/
public meta def bareHead (c : Char) : Bool := bareHeadClass.contains c

public meta def bareRest (c : Char) : Bool := bareRestClass.contains c

/-- Readable spellings for characters that would otherwise ride raw. The
    engine resolves these; anything else after the escape denotes itself. -/
public meta def stringEscapeSpelling (c : Char) : Option Char :=
  stringEscapes.lookup c

end SpytialLean.Sgq

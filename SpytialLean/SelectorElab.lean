module

public import Lean
public meta import SpytialLean.Selector
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Elab Meta

public section

/-! # SelectorElab — checked selector syntax

Selectors are Lean syntax (category `spytial_sel`), elaborated against a
`SelScope`: the vocabulary of sigs, relations, and constructor labels
the relationalizer can emit for the target type. Every identifier must resolve,
every operand must be of the kind its slot accepts, and every arity must check.
A renamed field or a typo is a compile error at the ident, not an empty
selection at render time.

The grammar and the checks are the engine's, read off the `Sgq` tables:
one parser rule per construct, built from its `template`; operand kinds from
`kinds`; widths from `arity`. Nothing below names a construct, so a construct
added upstream gets a rule, a kind check and an arity check by rebuilding.

What is written here is this package's own: the vocabulary and its hover
information, the constructor-label literal a spytial spec compares against, the
`raw` escape hatch, `let` (which the engine parses and refuses, and which we
desugar), and the leaves Lean's own lexer claims before any token table sees
them.

A scope is strict when the vocabulary is closed: a monomorphic type built from
monomorphic fields. A type parameter, a function field that does not tabulate,
a custom relationalizer, or a non-inductive in the closure makes it lenient. The
walker can then emit names no static analysis predicts, so unknown names warn
and pass through.
-/

/-! ## Scope -/

/-- Everything the relationalizer can emit for values of the target type, per
    `TypeShape`. -/
meta structure SelScope where
  root : Name
  /-- Lean type name → sig string, over the reachable field-type closure. -/
  types : Std.HashMap Name String := {}
  /-- Relation name → the emitting type and the walker's arity; `none`
      (`FieldShape.arity?`) leaves the name known and its width unchecked. -/
  rels : Std.HashMap String (Name × Option Nat) := {}
  /-- Constructor label → constructor, for `@:x = tt` literals. -/
  ctorLabels : Std.HashMap String Name := {}
  /-- Names introduced by earlier ops in the same spec (group names arity 1,
      inferred edges arity 2). -/
  introduced : Std.HashMap String Nat := {}
  /-- Open-world marker (see module docstring): unknown names become warnings. -/
  lenient : Bool := false
  deriving Inhabited

/-- Stop the closure walk where the walker stops decomposing. TODO: the walker
    still decomposes `Int`/`Char`/`UInt*` into constructor chains, so their
    closures must stay in the vocabulary until it treats them as scalars. -/
private meta def scalarTypes : List Name :=
  [``Nat, ``String, ``Float]

/-- `seeds` are extra types the value is known to contain — a container's type
    arguments, which the head constant alone cannot predict: `DA.FinAcc Seen2
    Letter` emits `Seen2`'s fields, but `DA.FinAcc`'s `tr` is a function over
    its own parameters and fixes no head to follow. -/
meta def SelScope.ofType (root : Name) (seeds : Array Name := #[]) : MetaM SelScope := do
  let env ← getEnv
  let mut scope : SelScope := { root }
  -- stuck matches appear in any open value; the walker emits one ternary
  scope := { scope with rels := scope.rels.insert "scrutinee" (root, some 3) }
  let mut queue : Array Name := #[root] ++ seeds
  let mut seen : NameSet := {}
  while !queue.isEmpty do
    let t := queue.back!
    queue := queue.pop
    if seen.contains t then continue
    seen := seen.insert t
    scope := { scope with types := scope.types.insert t (shortName t) }
    -- a custom relationalizer's emissions are its own: the world is open past it
    if (getSpytialRelationalizerName? env t).isSome then
      scope := { scope with lenient := true }
      continue
    if scalarTypes.contains t then
      continue
    match ← TypeShape.ofInductive t with
    | none =>
      scope := { scope with lenient := true }
    | some ts =>
      for c in ts.ctors do
        scope := { scope with ctorLabels := scope.ctorLabels.insert c.ctorShort c.ctorName }
        for f in c.fields do
          unless f.isProofLike do
            scope := { scope with rels := scope.rels.insert f.relName (t, f.arity?) }
            match f.table, f.typeHead with
            | some tbl, _ => queue := queue ++ tbl.columnHeads
            | none, some ft => queue := queue.push ft
            | none, none => scope := { scope with lenient := true }
  return scope

meta def SelScope.introduce (scope : SelScope) (name : String) (arity : Nat) : SelScope :=
  { scope with introduced := scope.introduced.insert name arity }

/-! ## Diagnostics -/

private meta def editDistance (a b : String) : Nat := Id.run do
  let s := a.toList.toArray
  let t := b.toList.toArray
  let mut prev := Array.range (t.size + 1)
  for i in [1:s.size + 1] do
    let mut curr := Array.replicate (t.size + 1) 0 |>.set! 0 i
    for j in [1:t.size + 1] do
      let cost := if s[i-1]! == t[j-1]! then 0 else 1
      curr := curr.set! j (min (min (prev[j]! + 1) (curr[j-1]! + 1)) (prev[j-1]! + cost))
    prev := curr
  return prev[t.size]!

private meta def sortDedup (xs : Array String) : Array String :=
  xs.qsort (· < ·) |>.foldl (init := #[]) fun acc s =>
    if acc.back? == some s then acc else acc.push s

private meta def SelScope.vocabulary (scope : SelScope) : Array String := Id.run do
  let mut out : Array String := #[]
  for (r, _) in scope.rels do out := out.push r
  for (_, s) in scope.types do out := out.push s
  for (n, _) in scope.introduced do out := out.push n
  return sortDedup out

private meta def suggest (scope : SelScope) (unknown : String) : String :=
  let vocab := scope.vocabulary
  let near := vocab.filter (fun v => editDistance unknown v ≤ 2)
  if !near.isEmpty then
    s!" (did you mean {", ".intercalate (near.toList.map (fun v => s!"'{v}'"))}?)"
  else if vocab.size ≤ 24 then
    s!"; vocabulary of '{scope.root}': {", ".intercalate vocab.toList}"
  else
    ""

/-- `U+XXXX` spelling, for a character with no printable form. -/
private meta def codepoint (c : Char) : String :=
  s!"U+{String.ofList ((Nat.toDigits 16 c.val.toNat).leftpad 4 '0') |>.toUpper}"

/-- Error in strict scopes, warning in lenient ones (the walker may emit names
    we cannot predict). Returns `recovery` when lenient. -/
private meta def unknownName {α} (scope : SelScope) (ref : Syntax) (what : String)
    (recovery : α) : TermElabM α := do
  let msg := m!"unknown {what}{suggest scope ref.getId.toString}"
  if scope.lenient then
    logWarningAt ref (msg ++ m!" — the vocabulary of '{scope.root}' is open (a \
      custom relationalizer, type parameter, or function field makes it \
      unpredictable), so the name passes through unchecked")
    return recovery
  else
    throwErrorAt ref msg

/-- Selector positions only: field-name positions (`edgeStyle`, `hideField`)
    act graph-side, where spec-introduced names do exist. -/
private meta def warnGraphSideName (ref : Syntax) (name : String) : TermElabM Unit :=
  logWarningAt ref s!"spec-introduced '{name}' exists only in the drawn graph — \
    the engine evaluates selectors against the data instance, so this reference \
    selects nothing at render"

/-! ## Syntax -/

open Lean Parser

/-! ### The category-local token table -/

/-- Whether Lean's identifier lexer spells `s`, which is exactly when a relation
    could be written with that name here and so exactly when a rule must not
    reserve it. The engine's own bare-name rule (`sgqBareName`) answers a
    different question — what the lowering quotes on the way out — and the two
    classes are not the same: `a/b` is bare to the engine and not an identifier
    here, `α` is an identifier here and not bare to the engine. -/
private meta def lexesAsIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs => isIdFirst c && cs.all isIdRest
  | [] => false

/-- The symbols the grammar lexes. A spelling Lean would read as an identifier
    is deliberately absent: it could be an ordinary field name, so the rules
    match it off the identifier instead of reserving it. -/
private meta def sgqSymbols : List String := Sgq.lexemes.filter (!lexesAsIdent ·)

/-- What Lean's quotation machinery lexes inside a selector: `$x`, `$x:ident`,
    `$_`, `$(e)`, `%$tk`, and the `$xs,*` splice, whose suffix `sepByElemParser`
    spells as the separator followed by `*` and lexes as one token. The colon,
    comma and parentheses are already the grammar's own. -/
private meta def antiquotSymbols : List String :=
  ["$", "_", "%", (Sgq.Construct.of .«quantifier» |>.part .«separator»).text ++ "*"]

/-- The table a selector lexes under. It is the engine's symbols and nothing
    else, so nothing here reaches the global table and none of Lean's own
    tokens reach a selector: a relation named `fun` needs no escape, and no
    longer Lean token can maximal-munch a shorter one of ours (`.` out of `.(`,
    `!` out of `!=`).

    The cost is that a `$(term)` antiquotation inside a selector can spell only
    what these tokens spell. Nothing in the package writes one. -/
private meta def selTokens : TokenTable :=
  (sgqSymbols ++ antiquotSymbols).foldl (fun t tk => t.insert tk tk) .empty

/-- `ParserCache.tokenCache` is not part of what `adaptUncacheableContextFn`
    resets, so a token lexed under one table would otherwise be served under the
    other at a region edge. -/
private meta def clearTokenCache (c : ParserContext) (s : ParserState) : ParserState :=
  { s with cache.tokenCache := { startPos := c.inputString.rawEndPos + ' ' } }

meta def withSelTokens (p : Parser) : Parser where
  info := p.info
  fn := fun c s =>
    clearTokenCache c <|
      adaptUncacheableContextFn (fun c => { c with tokens := selTokens })
        (fun c s => p.fn c (clearTokenCache c s)) c s

/-! ### The category

One category, as the engine has one grammar: a formula and a relational
expression sit in the same cascade, and which positions accept which is a
question about kinds, which the elaborator answers from the manifest.

`behavior := both` indexes an identifier under its own text as well, so a
keyword-led rule and a relation of the same name are both candidates and
longest-match decides between them. That is what keeps a field named `some`
writable without an escape. -/

declare_syntax_cat spytial_sel (behavior := both)

/-- Entry from Lean syntax, and the label a quotation of the language carries.
    Naming the category directly would parse it under Lean's token table. -/
meta def selExpr : Parser := withSelTokens (categoryParser `spytial_sel Sgq.loosest)

@[combinator_formatter selExpr] meta def selExpr.formatter :=
  PrettyPrinter.Formatter.categoryParser.formatter `spytial_sel
@[combinator_parenthesizer selExpr] meta def selExpr.parenthesizer :=
  PrettyPrinter.Parenthesizer.categoryParser.parenthesizer `spytial_sel Sgq.loosest

/-! ### Spellings -/

/-- One spelling, classified by `lexesAsIdent` rather than by a list. A symbol
    is an atom of the category-local table and so contributes nothing to the
    global one; a word is read off the identifier, which is what keeps it
    unreserved — and is the only reading that can ever match, since a word is
    not in the table for `symbolFn` to find.

    `trailing` says this spelling can be a trailing rule's first token.
    `trailingLoop` looks an identifier up under `identKind` only, so such a rule
    has to index itself there as well; a leading rule must not, because the
    category's `both` behaviour already finds it under the word and running it
    twice yields a `choice` node. -/
meta def spelledAs (s : String) (trailing : Bool := false) : Parser :=
  if lexesAsIdent s then nonReservedSymbol s (includeIdent := trailing)
  else { info := mkAtomicInfo s, fn := symbolFn s }

@[combinator_formatter spelledAs] meta def spelledAs.formatter (s : String) (_trailing := false) :=
  PrettyPrinter.Formatter.symbolNoAntiquot.formatter s
@[combinator_parenthesizer spelledAs] meta def spelledAs.parenthesizer (s : String) (_trailing := false) :=
  PrettyPrinter.Parenthesizer.symbolNoAntiquot.parenthesizer s

/-- Any spelling of an operator or a part: the engine accepts `or` and `||`
    alike, and an arrow's multiplicity is any of five words. The manifest gives
    every operator at least one, so the empty case is dead. -/
meta def anySpelling (trailing : Bool := false) : List String → Parser
  | [] => { fn := fun _ s => s.mkError "no spelling" }
  | s :: ss => ss.foldl (fun p s => p <|> spelledAs s trailing) (spelledAs s trailing)

/-- Which spelling was written is on the node, so the printers read it back off
    the atom rather than committing to one. -/
@[combinator_formatter anySpelling] meta def anySpelling.formatter (_trailing : Bool)
    (ss : List String) : PrettyPrinter.Formatter := do
  let stx ← Syntax.MonadTraverser.getCur
  PrettyPrinter.Formatter.symbolNoAntiquot.formatter
    ((ss.find? (stx.isToken ·)).getD (ss.headD ""))
@[combinator_parenthesizer anySpelling] meta def anySpelling.parenthesizer (_trailing : Bool)
    (ss : List String) : PrettyPrinter.Parenthesizer := do
  let stx ← Syntax.MonadTraverser.getCur
  PrettyPrinter.Parenthesizer.symbolNoAntiquot.parenthesizer
    ((ss.find? (stx.isToken ·)).getD (ss.headD ""))

/-! ### Identifiers

SGQ's identifier token cannot contain a `.`, so within a selector the dot is
only ever the join operator: `a.b` lexes as `a . b`, and both grammars read the
same text the same way with no spacing convention to remember. -/

/-- One identifier component: `identFnAux` without its `isIdCont` recursion.

    An escaped component still holds dots, which is how a qualified Lean name is
    written (`«Untyped.Term»`), and how a field whose name collides with a
    keyword stays reachable (`«univ»`) — `nonReservedSymbol` compares raw source
    text, which the escape changes. -/
meta def identComponentFn : ParserFn := fun c s =>
  let startPos := s.pos
  if h : c.atEnd startPos then s.mkEOIError
  else
    let curr := c.get' startPos h
    if isIdBeginEscape curr then
      let startPart := c.next' startPos h
      let s := takeUntilFn isIdEndEscape c (s.setPos startPart)
      if h : c.atEnd s.pos then
        s.mkUnexpectedErrorAt "unterminated identifier escape" startPart
      else
        let stopPart := s.pos
        let s := s.next' c s.pos h
        -- the escape spells a Lean name whole, so its dots are the name's
        mkIdResult startPos none
          ((c.extract startPart stopPart).splitOn "." |>.foldl Name.mkStr .anonymous) true c s
    else if isIdFirst curr then
      let s := takeWhileFn isIdRest c (s.next c startPos)
      mkIdResult startPos none (.str .anonymous (c.extract startPos s.pos)) true c s
    else
      s.mkErrorAt "identifier" startPos

-- `ident`'s antiquotation kind, so `$x:ident` still matches in a quotation.
meta def identComponent : Parser :=
  withAntiquot (mkAntiquot "ident" identKind)
    { fn := identComponentFn, info := mkAtomicInfo "ident" }
@[combinator_formatter identComponent] meta def identComponent.formatter :=
  Parser.ident.formatter
@[combinator_parenthesizer identComponent] meta def identComponent.parenthesizer :=
  Parser.ident.parenthesizer

/-! ### Rules from the template

`Sgq.Construct.template` gives a production in source order, so one builder
serves every construct. Each item contributes exactly one syntax child, which
is what lets the elaborator walk the same template over the parsed node. -/

/-- The node kind a construct's rule produces. -/
meta def nodeKind (c : Sgq.ConstructId) : SyntaxNodeKind :=
  `sgq ++ Name.mkSimple (Sgq.constructName c)

meta def binderGroupKind : SyntaxNodeKind := `sgqBinderGroup
meta def bindKind : SyntaxNodeKind := `sgqBind
meta def bodyKind : SyntaxNodeKind := `sgqBody

/-- `x, y : dom`, shared by comprehensions and quantifiers. -/
meta def binderGroup (cd : Sgq.Construct) (level : Nat) : Parser :=
  let sep := (cd.part .«separator»).text
  withAntiquot (mkAntiquot "sgqBinderGroup" binderGroupKind) <| node binderGroupKind
    (sepBy1 identComponent sep (psep := spelledAs sep) >>
      spelledAs (cd.part .«colon»).text >> categoryParser `spytial_sel level)

/-- `x = e`, a `let`'s binding. -/
meta def bindGroup (cd : Sgq.Construct) (level : Nat) : Parser :=
  node bindKind
    (identComponent >> spelledAs (cd.part .«bind»).text >> categoryParser `spytial_sel level)

/-- The parser for a run of template items. `trailing` is true while the next
    token could still be the rule's first, which decides whether a word spelling
    also indexes itself under `identKind`. -/
private meta partial def itemsParser (cd : Sgq.Construct) (trailing : Bool) :
    List Sgq.Item → Parser
  | [] => skip
  | item :: rest =>
    let sub (p : Parser) : Parser :=
      match rest with | [] => p | _ => p >> itemsParser cd false rest
    match item with
    | .operand level => sub (categoryParser `spytial_sel level)
    | .«repeat» level => sub (many (categoryParser `spytial_sel level))
    | .list level role =>
      let s := (cd.part role).text
      sub (sepBy (categoryParser `spytial_sel level) s (psep := spelledAs s))
    | .binders typed level =>
      let s := (cd.part .«separator»).text
      let g := if typed then binderGroup cd level else bindGroup cd level
      sub (sepBy1 g s (psep := spelledAs s))
    | .body level =>
      sub (node bodyKind (spelledAs (cd.part .«bar»).text >> categoryParser `spytial_sel level))
    | .name _ => sub identComponent
    | .constant | .operator => sub (anySpelling trailing cd.spellings)
    | .part role opt =>
      let p := anySpelling trailing (cd.part role).spellings
      if !opt then sub p
      -- A present-but-wrong reading has to be undone: `A -> one` writes a
      -- relation named `one`, not a multiplicity with no right operand.
      else match rest with
        | [] => Lean.Parser.optional p
        | _ =>
          let restP := itemsParser cd false rest
          Lean.Parser.atomic (p >> restP) <|> (pushNone >> restP)
    | Sgq.Item.«optional» inner =>
      sub (Lean.Parser.optional (Lean.Parser.atomic (itemsParser cd false inner)))

/-- Spellings Lean's own lexer claims before any token table sees them:
    `tokenFnAux` reads name, string, char and number literals structurally, so a
    rule keyed on one could never fire. The constructs they belong to are
    written out by hand below. -/
private meta def lexedByHost (s : String) : Bool :=
  if s.isEmpty then false
  else s.front == '`' || s.front == '"' || s.front == '\'' || s.front.isDigit

/-- Which constructs get a generated rule. Excluded: what the engine parses and
    refuses to run; an atom whose every spelling is an identifier, which an
    atom-keyed rule would never see on an unspaced `univ.lo` and which
    `resolveIdent` reads off the identifier instead; and a spelling Lean's lexer
    claims. `tests/SgqCoverageTest.lean` keeps the account. -/
meta def hasRule (cd : Sgq.Construct) : Bool :=
  cd.evaluates && !cd.template.isEmpty
    && !(cd.fixity == .atom && cd.spellings.all lexesAsIdent)
    && !cd.spellings.any lexedByHost
    && !(cd.template.any fun i => match i with | .constant => true | _ => false)

/-- A construct's rule. Trailing exactly when its production opens with an
    operand, which is what a left-recursive alternative looks like. -/
meta def ruleFor (c : Sgq.ConstructId) : Parser :=
  let cd := Sgq.Construct.of c
  match cd.template with
  | .operand lhs :: rest =>
    -- The one place this package narrows the engine: an op argument list is
    -- `spytialOpArg*`, so `hideAtom SBDD [a]` has to stay two arguments rather
    -- than becoming a box join.
    let body := itemsParser cd true rest
    let body := match rest with
      | .part .«open» _ :: _ => checkNoWsBefore >> body
      | _ => body
    trailingNode (nodeKind c) cd.prec lhs body
  | items => leadingNode (nodeKind c) cd.prec (itemsParser cd false items)

/-- Selector syntax is elaborated and lowered, never printed back — nothing in
    the package pretty-prints a `spytial_sel`, and there are no selector
    quotations. The parser attribute synthesises a formatter for every rule and
    cannot synthesise one for a template-driven `match`, so these say so rather
    than mirroring `itemsParser` in two further walks that only convention
    could keep in step. -/
@[combinator_formatter ruleFor] meta def ruleFor.formatter (_c : Sgq.ConstructId) :
    PrettyPrinter.Formatter := throwError "selector syntax is not pretty-printed"
@[combinator_parenthesizer ruleFor] meta def ruleFor.parenthesizer (_c : Sgq.ConstructId) :
    PrettyPrinter.Parenthesizer := throwError "selector syntax is not pretty-printed"

/-- The declaration `derive_sgq_rules` gives a construct's rule. The parser
    attribute keys the category on this name, so it is also how a test asks
    whether the rule was registered. -/
meta def ruleDeclName (c : Sgq.ConstructId) : Name :=
  `SpytialLean ++ Name.mkSimple s!"sgqRule_{Sgq.constructName c}"

/-- Declares one `@[spytial_sel_parser]` rule per construct that has one. The
    loop is over the manifest, so this is the whole grammar and it needs no
    edit when the cascade grows. -/
elab "derive_sgq_rules" : command => do
  for c in Sgq.allConstructs do
    let cd := Sgq.Construct.of c
    if hasRule cd then
      let name := (ruleDeclName c).components.getLast!
      let ty := if cd.template.head? matches some (.operand _) then `TrailingParser else `Parser
      let ctor := mkIdent (`SpytialLean.Sgq.ConstructId ++ Name.mkSimple (Sgq.constructName c))
      Command.elabCommand <| ← `(command|
        @[spytial_sel_parser] meta def $(mkIdent name) : $(mkIdent ty) := ruleFor $ctor)

derive_sgq_rules

/-! ### Leaves

Four literal forms and one construct that the generated rules cannot carry.
Numbers, strings and the backquoted atom literal are lexical rather than
constructs, and Lean's lexer reads them structurally. `let` the engine parses
and refuses; we desugar it by substitution, so it keeps a rule of its own. -/

meta def selIdentKind : SyntaxNodeKind := `selIdent
meta def selStrKind : SyntaxNodeKind := `selStr
meta def selNumKind : SyntaxNodeKind := `selNum
meta def selNegNumKind : SyntaxNodeKind := `selNegNum
meta def selAtomLitKind : SyntaxNodeKind := `selAtomLit

private meta def atomPrec : Nat := (Sgq.Construct.of .«name»).prec

@[spytial_sel_parser] meta def sgqIdentRule : Parser :=
  leadingNode selIdentKind atomPrec identComponent
@[spytial_sel_parser] meta def sgqStrRule : Parser :=
  leadingNode selStrKind atomPrec strLit
@[spytial_sel_parser] meta def sgqNumRule : Parser :=
  leadingNode selNumKind atomPrec numLit
@[spytial_sel_parser] meta def sgqNegNumRule : Parser :=
  leadingNode selNegNumKind atomPrec
    (spelledAs (Sgq.Construct.of .«constant» |>.part .«negation»).text >> checkNoWsBefore >> numLit)
/-- `` `a0 ``, spelled with Lean's name literal: `tokenFnAux` reads one
    structurally, before it ever consults a token table, so the backquote never
    reaches `symbolFn`. -/
@[spytial_sel_parser] meta def sgqAtomLitRule : Parser :=
  leadingNode selAtomLitKind (Sgq.Construct.of .«atomLiteral»).prec nameLit
/-- Desugared by substitution in the elaborator; the engine has no `let`. -/
@[spytial_sel_parser] meta def sgqLetRule : Parser := ruleFor .«let»

/-! ## Elaboration -/

/-- The typed result of elaborating a `spytial_sel`. Compile-time only; never
    stored. `arity` is `none` when statically unknown (`raw`, or a lenient
    pass-through), which disables downstream width checks. -/
meta structure EExpr where
  sel : Sel
  kind : Sgq.Kind
  arity : Option Nat := none
  deriving Inhabited

/-- A local binding introduced by a binder or a `let`. -/
meta inductive LocalBind where
  | binder                 -- ranges over a domain (arity 1)
  | letE (e : EExpr)       -- `let`-bound: substituted at use

/-- Ordered local environment (most-recent first); a later binder shadows an
    earlier `let` of the same name and vice versa. -/
meta abbrev LEnv := List (Name × LocalBind)

/-- Every construct that has a rule, by the node kind that rule produces. -/
private meta def constructOfKind : Std.HashMap Name Sgq.ConstructId :=
  Sgq.allConstructs.foldl (init := {}) fun m c => m.insert (nodeKind c) c

/-- Atom constructs read off an identifier rather than a rule of their own. -/
private meta def wordConstructs : List Sgq.ConstructId :=
  Sgq.allConstructs.filter fun c =>
    let cd := Sgq.Construct.of c
    cd.evaluates && cd.fixity == .atom && !cd.operators.isEmpty

private meta def kindName : Sgq.Kind → String
  | .relation => "a relational expression" | .number => "an integer expression"
  | .boolean => "a formula" | .«string» => "a label/literal value"
  | .operand => "an expression" | .any => "an expression"

/-- Whether a result of kind `got` fills a slot declared `want`. `operand` and
    `any` accept anything: the first hands its operand back, the second takes
    either side of a comparison. -/
private meta def kindAccepts (want : Option Sgq.Kind) (got : Sgq.Kind) : Bool :=
  match want with
  | none | some .any | some .operand => true
  | some k => k == got

/-- What a construct yields, given what its operands turned out to be. -/
private meta def yieldKind (declared : Option Sgq.Kind) (operands : Array Sgq.Kind) : Sgq.Kind :=
  match declared with
  | some .operand => operands[0]?.getD .relation
  | some k => k
  | none => .relation

/-! ### Widths -/

private meta def applyArity (ref : Syntax) (what : String) (a : Sgq.Arity)
    (slots : Array (Option Nat)) (extra : Array (Option Nat)) (binders : Nat) :
    TermElabM (Option Nat) := do
  for ((want, got), i) in (a.slots.toArray.zip slots).zipIdx do
    if let (some want, some got) := (want, got) then
      unless want == got do
        let which := if slots.size == 1 then "the operand" else s!"operand {i + 1}"
        throwErrorAt ref m!"{which} of {what} must have arity {want}, got {got}"
  if a.requires matches some .equal then
    let known := slots.filterMap id
    if let some first := known[0]? then
      unless known.all (· == first) do
        throwErrorAt ref m!"operands of {what} must have equal arity, got \
          {String.intercalate " and " (known.toList.map toString)}"
  let fold (xs : Array (Option Nat)) : TermElabM (Option Nat) := do
    let mut acc := xs[0]!
    for x in xs.extract 1 xs.size do
      match acc, x with
      | some a, some b =>
        if a + b < 3 then
          throwErrorAt ref m!"join of arity {a} and arity {b} has no columns left"
        acc := some (a + b - 2)
      | _, _ => acc := none
    return acc
  match a.yields with
  | none => return none
  | some (.fixed n) => return some n
  | some (.slot i) => return slots[i]!
  | some .«sum» =>
    match slots[0]!, slots[1]! with
    | some a, some b => return some (a + b)
    | _, _ => return none
  | some .«join» => fold slots
  | some .boxJoin => fold (slots ++ extra)
  | some .binders => return some binders

/-! ### Names -/

/-- Adds hover/go-to-def info on success. -/
private meta def resolveGlobal? (stx : Syntax) : TermElabM (Option Name) := do
  try
    pure (some (← realizeGlobalConstNoOverloadWithInfo stx))
  catch _ =>
    pure none

/-- Hover/go-to-def for a relation name, which is not a Lean identifier. Aim at
    the projection when the owner is a structure, else at the owner type — a
    non-structure field is written in its constructors. -/
private meta def addRelInfo (stx : Syntax) (owner : Name) (relName : String) :
    TermElabM Unit := do
  let env ← getEnv
  let proj := Name.mkStr owner relName
  let target := if env.contains proj then proj else owner
  if env.contains target then
    addConstInfo stx target

/-- The constructor label a bare ident denotes, with hover info. -/
private meta def resolveCtorLit? (scope : SelScope) (stx : Syntax) : TermElabM (Option Sel) := do
  if let some ctorName := scope.ctorLabels.get? (stx.getId.toString (escape := false)) then
    if let some e ← try pure (some (← mkConstWithLevelParams ctorName)) catch _ => pure none then
      discard <| Term.addTermInfo stx e
    return some (.ctorLit ctorName (shortName ctorName))
  return none

/-- Builtins are named, not spelled: the engine's own lists are the vocabulary,
    and the list a name is in gives its arity. -/
private meta def builtinArity? (s : String) : Option Nat :=
  if Sgq.binaryBuiltins.contains s then some 2
  else if Sgq.unaryBuiltins.contains s then some 1
  else none

/-- Which operator a node was written with. Spellings are unique within a
    construct, so the atom the `.operator` item took decides. -/
private meta def opWritten? (cd : Sgq.Construct) (stx : Syntax) : Option Sgq.OpId := do
  cd.operatorSpelled (stx[← cd.template.findIdx? (· matches .operator)].getAtomVal)

/-- What a subexpression yields, read off its node without elaborating it.
    Needed where a slot accepts `any` and the operands have to agree: a bare
    identifier opposite a label is a constructor label, not a relation, and
    resolving it as a relation first would report the wrong error. -/
private meta def declaredKind? (stx : Syntax) : Option Sgq.Kind :=
  let k := stx.getKind
  if k == selStrKind then some .«string»
  else if k == selNumKind || k == selNegNumKind then some .number
  else match constructOfKind.get? k with
    | some c =>
      let cd := Sgq.Construct.of c
      match opWritten? cd stx with
      | some o => (Sgq.Op.of o).kinds.yields
      | none => cd.kinds.yields
    | none => none

/-- A relational expression opposite a value: only a bare ident makes sense, as
    a constructor-label literal, or as `true`/`false` against `@bool:`. -/
private meta def coerceVal (scope : SelScope) (stx : Syntax) (wantBool : Bool) :
    TermElabM EExpr := do
  unless stx.isOfKind selIdentKind do
    throwErrorAt stx "cannot compare a label value with this operand; a label \
      value compares against a constructor or a string literal — for a numeric \
      label, project with `@num:`"
  let x := stx[0]
  if wantBool then
    match x.getId.toString with
    | "true" => return { sel := .boolLit true, kind := .boolean }
    | "false" => return { sel := .boolLit false, kind := .boolean }
    | _ => pure ()
  if let some v ← resolveCtorLit? scope x then
    return { sel := v, kind := .«string» }
  let some constName ← resolveGlobal? x
    | throwErrorAt x m!"unknown constructor label '{x.getId}'; known labels of \
        '{scope.root}': {", ".intercalate (sortDedup (scope.ctorLabels.toList.map (·.1)).toArray).toList}"
  match (← getEnv).find? constName with
  | some (.ctorInfo ci) =>
    if !scope.types.contains ci.induct && !scope.lenient then
      throwErrorAt x m!"constructor '{constName}' belongs to '{ci.induct}', \
        which cannot occur in values of '{scope.root}'"
    return { sel := .ctorLit constName (shortName constName), kind := .«string» }
  | _ =>
    throwErrorAt x m!"'{constName}' is not a constructor; label comparisons \
      expect a constructor or a literal"

mutual

private meta partial def elabExpr (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM EExpr := do
  let k := stx.getKind
  if k == selIdentKind then
    resolveIdent scope env ⟨stx[0]⟩
  else if k == selStrKind then
    let s := stx[0]
    if let some c := sgqUnspellableChar? (s.isStrLit?.getD "") then
      throwErrorAt s m!"string literal contains {codepoint c} — SGQ's string \
        syntax has no escape for it, and it cannot ride raw through the spec"
    return { sel := .str (s.isStrLit?.getD ""), kind := .«string» }
  else if k == selNumKind then
    return { sel := .num (Int.ofNat (stx[0].isNatLit?.getD 0)), kind := .number }
  else if k == selNegNumKind then
    return { sel := .num (-(Int.ofNat (stx[1].isNatLit?.getD 0))), kind := .number }
  else if k == selAtomLitKind then
    match stx[0].isNameLit? with
    | some n =>
      return { sel := .node .«atomLiteral» (Sgq.Construct.of .«atomLiteral»).operators.head?
                 #[.name n.toString],
               kind := .relation, arity := some 1 }
    | none => throwErrorAt stx "malformed atom literal"
  else if k == nodeKind .«let» then
    elabLet scope env stx
  else match constructOfKind.get? k with
    | some c => elabNode scope env stx c
    | none => throwErrorAt stx "unexpected selector syntax"

/-- Elaborates one construct by walking its template against the parsed node:
    each item takes exactly one child, in order. -/
private meta partial def elabNode (scope : SelScope) (env : LEnv) (stx : Syntax)
    (c : Sgq.ConstructId) : TermElabM EExpr := do
  let cd := Sgq.Construct.of c
  -- A bracket that only changes precedence yields its operand unchanged, so it
  -- is not kept: the renderer re-derives parentheses from the cascade.
  if cd.kinds.yields == some .operand && cd.kinds.operands == [Option.some .operand] then
    if let some i := cd.template.findIdx? (· matches .operand _) then
      return ← elabExpr scope env stx[i]
  -- A construct that does not settle its own kind may be a builtin call rather
  -- than what its operands make of it: `add[1, 2]` is a call and `f[a]` a join,
  -- and only the callee says which.
  if cd.kinds.yields.isNone then
    if let some e ← elabBuiltinCall? scope env stx c then return e
  let op? := opWritten? cd stx
  let kinds := match op? with | some o => (Sgq.Op.of o).kinds | none => cd.kinds
  let arity := match op? with | some o => (Sgq.Op.of o).arity | none => cd.arity
  let what : String := match op? with
    | some o => (Sgq.Op.of o).text
    | none => s!"a {Sgq.constructName c}"
  if let some o := op? then
    unless (Sgq.Op.of o).evaluates do
      throwErrorAt stx m!"the engine parses '{what}' and refuses to evaluate it"
  let mut args : Array Arg := #[]
  let mut slots : Array (Option Nat) := #[]
  let mut opKinds : Array Sgq.Kind := #[]
  let mut extra : Array (Option Nat) := #[]
  let mut binders : Nat := 0
  let mut env := env
  let mut negated := false
  for (item, i) in cd.template.toArray.zipIdx do
    match item with
    | .operand _ =>
      let want := kinds.operands[slots.size]?.getD none
      let e ← elabOperand scope env stx cd want slots.size i
      args := args.push (.expr e.sel)
      slots := slots.push e.arity
      opKinds := opKinds.push e.kind
    | .body _ =>
      let e ← elabAt scope env stx[i][1] kinds.inner
      args := args.push (.expr e.sel)
    | .«repeat» _ =>
      let es ← stx[i].getArgs.mapM fun a => elabAt scope env a kinds.inner
      args := args.push (.exprs (es.map (·.sel)))
    | .list _ _ =>
      let es ← stx[i].getSepArgs.mapM fun a => elabAt scope env a none
      args := args.push (.exprs (es.map (·.sel)))
      extra := es.map (·.arity)
    | .binders typed _ =>
      let (bs, env') ← elabBinders scope env typed (Sgq.constructName c) stx[i].getSepArgs
      args := args.push (.binders bs)
      binders := binders + bs.size
      env := env'
    | .name _ => args := args.push (.name stx[i].getId.toString)
    | .part role opt =>
      if opt then
        let s := stx[i].getAtomVal
        if role == .«negation» && !s.isEmpty then negated := true
        args := args.push (.atom (if s.isEmpty then none else some s))
    | Sgq.Item.«optional» inner =>
      let present := stx[i].getNumArgs != 0
      args := args.push (.atom (if present then some "" else none))
      if present then
        for (item, j) in inner.toArray.zipIdx do
          if let .operand _ := item then
            let e ← elabAt scope env stx[i][j] kinds.operands[slots.size]!
            args := args.push (.expr e.sel)
            slots := slots.push e.arity
            opKinds := opKinds.push e.kind
    | .operator | .constant => pure ()
  -- A negated comparison lowers by prefixing the operator, which only has a
  -- meaning where the engine spells the negation that way.
  if negated && kinds.operands.any (· == some .number) then
    throwErrorAt stx m!"a negated numeric comparison has no lowering; write the \
      opposite operator"
  -- Slots that accept either side have to agree with each other: the engine
  -- compares like with like, so `#a = b` is a mistake rather than a coercion.
  if kinds.operands.any (· == Option.some .any) then
    for k in opKinds do
      unless k == opKinds[0]! do
        throwErrorAt stx m!"cannot compare {kindName opKinds[0]!} with {kindName k}"
  if arity.yields matches some .boxJoin && extra.isEmpty then
    throwErrorAt stx "box join needs at least one argument (`a[b]` means `b.a`)"
  let width ← applyArity stx what arity slots extra binders
  return { sel := .node c op? args, kind := yieldKind kinds.yields opKinds, arity := width }

/-- One operand slot. A slot declared `any` takes either side of a comparison,
    so what the *other* slot yields decides how a bare identifier here reads: a
    label or a boolean opposite it makes this one a constructor label. -/
private meta partial def elabOperand (scope : SelScope) (env : LEnv) (stx : Syntax)
    (cd : Sgq.Construct) (want : Option Sgq.Kind) (slot i : Nat) : TermElabM EExpr := do
  if want == some .any && stx[i].isOfKind selIdentKind then
    let others := cd.template.toArray.zipIdx.filterMap fun (it, j) =>
      if it matches .operand _ then some j else none
    let mut valued : Option Sgq.Kind := none
    for (j, n) in others.zipIdx do
      if n != slot then
        if let some k := declaredKind? stx[j] then
          if k == .«string» || k == .boolean then valued := some k
    if let some k := valued then
      return ← coerceVal scope stx[i] (k == .boolean)
  elabAt scope env stx[i] want

/-- `add[1, 2]`, `abs[x]`, `sum[e]`: a bracket whose callee names one of the
    engine's builtins is a call, not a box join. The lists are the engine's and
    the list a name is in gives its arity, so nothing here enumerates them. -/
private meta partial def elabBuiltinCall? (scope : SelScope) (env : LEnv) (stx : Syntax)
    (c : Sgq.ConstructId) : TermElabM (Option EExpr) := do
  let cd := Sgq.Construct.of c
  let some ci := cd.template.findIdx? (· matches .operand _) | return none
  let some li := cd.template.findIdx? (· matches .list _ _) | return none
  unless stx[ci].isOfKind selIdentKind do return none
  let callee := stx[ci][0]
  if (env.lookup callee.getId).isSome then return none
  let name := callee.getId.toString
  let args := stx[li].getSepArgs
  if let some n := builtinArity? name then
    unless args.size == n do
      throwErrorAt stx m!"'{name}' takes {n} integer argument(s), got {args.size}"
    let es ← args.mapM fun a => elabAt scope env a (some .number)
    return some { sel := .node c none #[.expr (.builtin name), .exprs (es.map (·.sel))],
                  kind := .number }
  if Sgq.setBuiltins.contains name then
    unless args.size == 1 do
      throwErrorAt stx m!"'{name}[e]' takes one relational argument, got {args.size}"
    let e ← elabAt scope env args[0]! (some .relation)
    if let some a := e.arity then
      unless a == 1 do
        throwErrorAt args[0]! m!"the argument of {name}[e] must have arity 1, got {a}"
    -- Aggregators read numeric values; walker atom ids are opaque (`atom_N`),
    -- and the value is the label — so decode via the engine's own projection.
    let proj := Sgq.Op.of .«labelNumber»
    let inner : Sel := .node proj.construct (some proj.id) #[.expr e.sel]
    return some { sel := .node c none #[.expr (.builtin name), .exprs #[inner]],
                  kind := .number }
  return none

/-- Elaborates `stx` and checks it against the kind its slot accepts. A slot
    declared `any` takes either side of a comparison, so the two operands are
    reconciled against each other instead (`elabAt` is called with `none` and
    `elabNode` compares what came back). -/
private meta partial def elabAt (scope : SelScope) (env : LEnv) (stx : Syntax)
    (want : Option Sgq.Kind) : TermElabM EExpr := do
  let e ← elabExpr scope env stx
  unless kindAccepts want e.kind do
    throwErrorAt stx m!"this position expects {kindName (want.getD .relation)}, but \
      the selector is {kindName e.kind}"
  return e

private meta partial def elabBinders (scope : SelScope) (env : LEnv) (typed : Bool)
    (what : String) (groups : Array Syntax) : TermElabM (Array (Name × Sel) × LEnv) := do
  let mut binders : Array (Name × Sel) := #[]
  let mut env := env
  for group in groups do
    if typed then
      let dom ← elabAt scope env group[2] (some .relation)
      -- Not the engine's rule, ours: it ranges a binder over the *atoms* of a
      -- wider domain, which is never what the source meant.
      if let some a := dom.arity then
        unless a == 1 do
          throwErrorAt group[2] m!"a {what} binder domain must have arity 1, got {a}"
      for x in group[0].getSepArgs do
        binders := binders.push (x.getId, dom.sel)
        env := (x.getId, .binder) :: env
    else
      -- a `let` binding is substituted at use, so it never becomes a binder
      let e ← elabExpr scope env group[2]
      env := (group[0].getId, .letE e) :: env
      binders := binders.push (group[0].getId, e.sel)
  if binders.isEmpty then throwError s!"a {what} needs at least one binder"
  return (binders, env)

/-- `let` desugars by substitution — SGQ has no `let`. A later binder shadows
    the `let`. -/
private meta partial def elabLet (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM EExpr := do
  let (_, env') ← elabBinders scope env false "let" stx[1].getSepArgs
  elabExpr scope env' stx[2][1]

/-- Resolution order: the engine's own word constants, a local binding, a
    constructor label, then the vocabulary. -/
private meta partial def resolveIdent (scope : SelScope) (env : LEnv)
    (stx : TSyntax `ident) : TermElabM EExpr := do
  -- Source text, not the name, decides: `«univ»` is a field spelled differently
  -- that parses to the same `Name`.
  if let .ident _ raw _ _ := stx.raw then
    for c in wordConstructs do
      for o in (Sgq.Construct.of c).operators do
        let od := Sgq.Op.of o
        if od.spellings.contains raw.toString then
          let width ← applyArity stx od.text od.arity #[] #[] 0
          return { sel := .node c (some o) #[], kind := od.kinds.yields.getD .relation,
                   arity := width }
  let name := stx.getId
  if let some bind := env.lookup name then
    match bind with
    | .binder => return { sel := .var name, kind := .relation, arity := some 1 }
    | .letE e =>
      -- Lowering is name-based, so a binder introduced after the `let` would
      -- silently capture the substituted expression's free variables.
      let fvs := e.sel.freeVars
      for (n, b) in env do
        if n == name then break
        if b matches .binder then
          if fvs.contains n then
            throwErrorAt stx m!"cannot use let-bound '{name}' here: it refers \
              to '{n}', which a nearer binder shadows — the substitution would \
              be captured; rename the inner binder"
      return e
  if let some v ← resolveCtorLit? scope stx then
    return { sel := v, kind := .«string» }
  let s := name.toString (escape := false)
  if let some (owner, arity?) := scope.rels.get? s then
    addRelInfo stx owner s
    return { sel := .rel s, kind := .relation, arity := arity? }
  if let some arity := scope.introduced.get? s then
    warnGraphSideName stx s
    return { sel := .rel s, kind := .relation, arity := some arity }
  if let some e ← resolveTypeRef? then return e
  unknownName scope stx s!"name '{s}'" { sel := Sel.rel s, kind := .relation }
where
  resolveTypeRef? : TermElabM (Option EExpr) := do
    let some constName ← resolveGlobal? stx | return none
    match (← getEnv).find? constName with
    | some (.inductInfo _) =>
      if scope.types.contains constName || scope.lenient then
        return some { sel := .sig constName (shortName constName), kind := .relation,
                      arity := some 1 }
      else
        throwErrorAt stx m!"type '{constName}' cannot occur in values of \
          '{scope.root}'{suggest scope (shortName constName)}"
    | some (.ctorInfo _) =>
      throwErrorAt stx m!"'{constName}' is a constructor — constructor literals \
        only occur in label comparisons (e.g. `@:x = {shortName constName}`)"
    | _ => return none

end

/-! ## Entry points -/

/-- `pair` positions project first/last at runtime, so a wider selector warns
    rather than errors. An `edge` position reads the whole tuple, so any width
    from 2 up passes. `nary` positions read whole tuples of any width. -/
meta inductive ArityExpect where
  | unary
  | pair
  | edge
  | unaryOrPair
  | nary
  deriving Repr, Inhabited

/-- A whole-selector string literal is the raw escape hatch. -/
meta def elabSelector (scope : SelScope) (expect : ArityExpect)
    (stx : TSyntax `spytial_sel) : TermElabM Sel := do
  if stx.raw.isOfKind selStrKind then
    if let some s := stx.raw[0].isStrLit? then
      return .raw s
  let e ← elabExpr scope [] stx
  unless e.kind == .relation do
    throwErrorAt stx m!"a selector picks out atoms or tuples, but this is \
      {kindName e.kind}"
  if let some a := e.arity then
    match expect with
    | .unary =>
      unless a == 1 do
        throwErrorAt stx m!"this position selects atoms (arity 1), but the \
          selector has arity {a}"
    | .pair =>
      if a < 2 then
        throwErrorAt stx m!"this position selects pairs (arity 2), but the \
          selector has arity {a}"
      else if a > 2 then
        logWarningAt stx m!"arity-{a} selector in a pair position: only the \
          first and last columns of each tuple are used"
    | .edge =>
      if a < 2 then
        throwErrorAt stx m!"this position selects edges (arity 2 or wider: \
          source, then label columns, then target), but the selector has \
          arity {a}"
    | .unaryOrPair =>
      unless a == 1 || a == 2 do
        throwErrorAt stx m!"this position selects atoms or pairs (arity 1 or \
          2), but the selector has arity {a}"
    | .nary => pure ()
  return e.sel

meta def elabFieldName (scope : SelScope) (stx : TSyntax `ident) : TermElabM String := do
  let s := stx.getId.toString (escape := false)
  if scope.rels.contains s || scope.introduced.contains s then
    return s
  unknownName scope stx s!"relation '{s}'" s

end

end SpytialLean

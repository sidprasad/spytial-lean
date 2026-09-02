module

public import Lean
public meta import Lean.Data.EditDistance
public meta import SpytialLean.Selector
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.LeanSelector

namespace SpytialLean

open Lean Elab Meta

public section

/-! # SelectorElab — checked selector syntax

The grammar and the checks are read off the `Sgq` tables. Nothing below names a
construct.

A scope is strict when the vocabulary is closed: a monomorphic type built from
monomorphic fields. A type parameter, a function field that does not tabulate, a
custom relationalizer, or a non-inductive in the closure makes it lenient, and
the walker can then emit names no static analysis predicts — so unknown names
warn and pass through.
-/

/-- A name an earlier op put into the drawn graph. `referencedBy` is the
    `item.field` positions where the engine resolves it; a reference from
    anywhere else parses and is never looked up. -/
meta structure Introduced where
  arity : Nat
  referencedBy : List String
  deriving Inhabited

/-- Everything the relationalizer can emit for values of the target type. -/
meta structure SelScope where
  root : Name
  /-- Lean type name → sig string, over the reachable field-type closure. -/
  types : Std.HashMap Name String := {}
  /-- Relation name → emitting type and walker arity; `none` leaves the width
      unchecked. -/
  rels : Std.HashMap String (Name × Option Nat) := {}
  /-- Constructor label → constructor, for `@:x = tt` literals. -/
  ctorLabels : Std.HashMap String Name := {}
  introduced : Std.HashMap String Introduced := {}
  /-- Open-world marker (see module docstring): unknown names become warnings. -/
  lenient : Bool := false
  deriving Inhabited

/-- Stop the closure walk where the walker stops decomposing. TODO: the walker
    still decomposes `Int`/`Char`/`UInt*` into constructor chains, so their
    closures must stay in the vocabulary until it treats them as scalars. -/
private meta def scalarTypes : List Name :=
  [``Nat, ``String, ``Float]

/-- `seeds` are types the head constant alone cannot predict: `DA.FinAcc Seen2
    Letter` emits `Seen2`'s fields, but `tr` is a function over `DA.FinAcc`'s
    own parameters and fixes no head to follow. -/
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

meta def SelScope.introduce (scope : SelScope) (name : String) (i : Introduced) :
    SelScope :=
  { scope with introduced := scope.introduced.insert name i }

/-- Union of two scopes, for a value view whose positive facts span several
    types. Lenient if either side is; a relation name claimed at two
    different arities keeps the name with its width unchecked. -/
meta def SelScope.merge (a b : SelScope) : SelScope := Id.run do
  let mut rels := a.rels
  for (n, owner, arity?) in b.rels do
    rels := match rels.get? n with
      | some (o, a?) => if a? == arity? then rels else rels.insert n (o, none)
      | none => rels.insert n (owner, arity?)
  return { root := a.root
           types := b.types.fold (init := a.types) fun m k v => m.insert k v
           rels
           ctorLabels := b.ctorLabels.fold (init := a.ctorLabels) fun m k v => m.insert k v
           introduced := b.introduced.fold (init := a.introduced) fun m k v => m.insert k v
           lenient := a.lenient || b.lenient }

/-! ## Diagnostics -/

private meta def sortDedup (xs : Array String) : Array String :=
  xs.qsort (· < ·) |>.eraseReps

private meta def SelScope.vocabulary (scope : SelScope) : Array String := Id.run do
  let mut out : Array String := #[]
  for (r, _) in scope.rels do out := out.push r
  for (_, s) in scope.types do out := out.push s
  for (n, _) in scope.introduced do out := out.push n
  return sortDedup out

private meta def suggest (scope : SelScope) (unknown : String) : String :=
  let vocab := scope.vocabulary
  -- Cutoff 2 bounds the cost, not the result: a returned distance may exceed it.
  let near := vocab.filter fun v => (EditDistance.levenshtein unknown v 2).any (· ≤ 2)
  if !near.isEmpty then
    s!" (did you mean {", ".intercalate (near.toList.map (fun v => s!"'{v}'"))}?)"
  else if vocab.size ≤ 24 then
    s!"; vocabulary of '{scope.root}': {", ".intercalate vocab.toList}"
  else
    ""

private meta def codepoint (c : Char) : String :=
  s!"U+{String.ofList ((Nat.toDigits 16 c.val.toNat).leftpad 4 '0') |>.toUpper}"

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

private meta def warnGraphSideName (ref : Syntax) (name : String) : TermElabM Unit :=
  logWarningAt ref s!"spec-introduced '{name}' exists only in the drawn graph — \
    the engine evaluates selectors against the data instance, so this reference \
    selects nothing at render"

private meta def warnUnresolvedName (ref : Syntax) (position name : String) :
    TermElabM Unit :=
  logWarningAt ref s!"spec-introduced '{name}' is not resolved at {position} — \
    the engine matches that field before groups and inferred edges join the \
    drawn graph, so this reference matches nothing at render"

/-! ## Syntax -/

open Lean Parser

/-! ### The category-local token table -/

/-- Exactly when a relation could be written with that name here, and so when a
    rule must not reserve it. Not the engine's `sgqBareName` class, which is the
    *output* alphabet: `a/b` is bare there and no identifier here, `α` here and
    not bare there. -/
private meta def lexesAsIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs => isIdFirst c && cs.all isIdRest
  | [] => false

private meta def sgqSymbols : List String := Sgq.lexemes.filter (!lexesAsIdent ·)

/-- What Lean's quotation machinery lexes inside a selector, read off
    `mkAntiquot`, `mkAntiquotSplice` and `sepByElemParser` at v4.32.2. The
    `$xs,*` splice suffix is the separator plus `*`, lexed as one token. -/
private meta def antiquotSymbols : List String :=
  ["$", "_", "%", (Sgq.Construct.of .«quantifier» |>.part .«separator»).text ++ "*"]

/-- Nothing here reaches the global table and none of Lean's tokens reach a
    selector, so a relation named `fun` needs no escape. Cost: a `$(term)`
    antiquotation lexes under this table too. Nothing in the package writes one. -/
private meta def selTokens : TokenTable :=
  (sgqSymbols ++ antiquotSymbols).foldl (fun t tk => t.insert tk tk) .empty

/-- `ParserCache.tokenCache` is not part of what `adaptUncacheableContextFn`
    resets, so at a region boundary the one-entry cache can replay a token
    lexed under the other table. -/
private meta def clearTokenCache (c : ParserContext) (s : ParserState) : ParserState :=
  { s with cache.tokenCache := { startPos := c.inputString.rawEndPos + ' ' } }

private meta def withTokens (tokens : ParserContextCore → TokenTable) (p : Parser) :
    Parser where
  info := p.info
  fn := fun c s =>
    clearTokenCache c <|
      adaptUncacheableContextFn (fun c => { c with tokens := tokens c })
        (fun c s => p.fn c (clearTokenCache c s)) c s

meta def withSelTokens (p : Parser) : Parser := withTokens (fun _ => selTokens) p

/-- Under `selTokens` a Lean term's own tokens do not lex at all. -/
meta def withHostTokens (p : Parser) : Parser := withTokens (fun c => getTokenTable c.env) p

@[combinator_formatter withHostTokens] meta def withHostTokens.formatter
    (p : PrettyPrinter.Formatter) : PrettyPrinter.Formatter := p
@[combinator_parenthesizer withHostTokens] meta def withHostTokens.parenthesizer
    (p : PrettyPrinter.Parenthesizer) : PrettyPrinter.Parenthesizer := p

/-! ### The category

`behavior := both` also indexes an identifier-spelled leading rule under the
identifier's own text, so a keyword-led rule and a relation of the same name are
both candidates and longest-match decides — which keeps a field named `some`
writable without an escape. -/

declare_syntax_cat spytial_sel (behavior := both)

/-- Naming the category directly would parse it under Lean's token table. -/
meta def selExpr : Parser := withSelTokens (categoryParser `spytial_sel Sgq.loosest)

@[combinator_formatter selExpr] meta def selExpr.formatter :=
  PrettyPrinter.Formatter.categoryParser.formatter `spytial_sel
@[combinator_parenthesizer selExpr] meta def selExpr.parenthesizer :=
  PrettyPrinter.Parenthesizer.categoryParser.parenthesizer `spytial_sel Sgq.loosest

/-- `trailingLoop` looks an identifier up under `identKind` only, so a trailing
    rule has to index itself there as well; a leading rule must not, because
    `both` already finds it under the word and running it twice yields a
    `choice` node. -/
meta def spelledAs (s : String) (trailing : Bool := false) : Parser :=
  if lexesAsIdent s then nonReservedSymbol s (includeIdent := trailing)
  else { info := mkAtomicInfo s, fn := symbolFn s }

@[combinator_formatter spelledAs] meta def spelledAs.formatter (s : String) (_trailing := false) :=
  PrettyPrinter.Formatter.symbolNoAntiquot.formatter s
@[combinator_parenthesizer spelledAs] meta def spelledAs.parenthesizer (s : String) (_trailing := false) :=
  PrettyPrinter.Parenthesizer.symbolNoAntiquot.parenthesizer s

/-- The manifest gives every operator at least one spelling, so `[]` is dead. -/
meta def anySpelling (trailing : Bool := false) : List String → Parser
  | [] => { fn := fun _ s => s.mkError "no spelling" }
  | s :: ss => ss.foldl (fun p s => p <|> spelledAs s trailing) (spelledAs s trailing)

/-- Which spelling was written is on the node, so read it back off the atom. -/
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

/-- `identFnAux` without the `isIdCont` recursion, which would merge `a.b` into
    one dotted name where the dot is the join operator. An escape keeps a
    keyword-named field reachable (`«univ»`) — `nonReservedSymbol` compares raw
    source text, which the escape changes. -/
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

Each template item contributes exactly one syntax child, which is what lets the
elaborator walk the same template over the parsed node. -/

meta def nodeKind (c : Sgq.ConstructId) : SyntaxNodeKind :=
  `sgq ++ Name.mkSimple (Sgq.constructName c)

meta def binderGroupKind : SyntaxNodeKind := `sgqBinderGroup
meta def bindKind : SyntaxNodeKind := `sgqBind
meta def bodyKind : SyntaxNodeKind := `sgqBody

meta def binderGroup (cd : Sgq.Construct) (level : Nat) : Parser :=
  let sep := (cd.part .«separator»).text
  withAntiquot (mkAntiquot "sgqBinderGroup" binderGroupKind) <| node binderGroupKind
    (sepBy1 identComponent sep (psep := spelledAs sep) >>
      spelledAs (cd.part .«colon»).text >> categoryParser `spytial_sel level)

meta def bindGroup (cd : Sgq.Construct) (level : Nat) : Parser :=
  node bindKind
    (identComponent >> spelledAs (cd.part .«bind»).text >> categoryParser `spytial_sel level)

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
      -- `A -> one` writes a relation named `one`, not a multiplicity missing its
      -- right operand; `elabNode` reads the atom off the position, so push a null
      else
        let restP := itemsParser cd false rest
        Lean.Parser.atomic (p >> restP) <|> (pushNone >> restP)
    | Sgq.Item.«optional» inner =>
      sub (Lean.Parser.optional (Lean.Parser.atomic (itemsParser cd false inner)))

/-- `tokenFnAux` reads name, string, char and number literals structurally,
    before any token table sees them, so a rule keyed on one could never fire. -/
private meta def lexedByHost (s : String) : Bool :=
  if s.isEmpty then false
  else s.front == '`' || s.front == '"' || s.front == '\'' || s.front.isDigit

/-- An all-identifier atom is excluded because an atom-keyed rule would never
    see it on an unspaced `univ.lo`; `resolveIdent` reads it off the identifier
    instead. `SpytialTests/SgqCoverageTest.lean` keeps the account. -/
meta def hasRule (cd : Sgq.Construct) : Bool :=
  cd.evaluates && !cd.template.isEmpty
    && !(cd.fixity == .atom && cd.spellings.all lexesAsIdent)
    && !cd.spellings.any lexedByHost
    && !(cd.template.any fun i => match i with | .constant => true | _ => false)

meta def ruleFor (c : Sgq.ConstructId) : Parser :=
  let cd := Sgq.Construct.of c
  match cd.template with
  | .operand lhs :: rest =>
    -- the engine accepts `f [x]` as a box join; requiring adjacency is the one
    -- place we narrow it, and keeps `hideAtom SBDD [a]` two op arguments
    let body := itemsParser cd true rest
    let body := match rest with
      | .part .«open» _ :: _ => checkNoWsBefore >> body
      | _ => body
    trailingNode (nodeKind c) cd.prec lhs body
  | items => leadingNode (nodeKind c) cd.prec (itemsParser cd false items)

/-- Selector syntax is never printed back. The parser attribute demands a
    formatter per rule and cannot synthesise one for a template-driven `match`,
    and mirroring `itemsParser` twice more only convention could keep in step. -/
@[combinator_formatter ruleFor] meta def ruleFor.formatter (_c : Sgq.ConstructId) :
    PrettyPrinter.Formatter := throwError "selector syntax is not pretty-printed"
@[combinator_parenthesizer ruleFor] meta def ruleFor.parenthesizer (_c : Sgq.ConstructId) :
    PrettyPrinter.Parenthesizer := throwError "selector syntax is not pretty-printed"

/-- The parser attribute keys the category on this name, so a test can ask it. -/
meta def ruleDeclName (c : Sgq.ConstructId) : Name :=
  `SpytialLean ++ Name.mkSimple s!"sgqRule_{Sgq.constructName c}"

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

meta def selIdentKind : SyntaxNodeKind := `selIdent
meta def selStrKind : SyntaxNodeKind := `selStr
meta def selNumKind : SyntaxNodeKind := `selNum
meta def selNegNumKind : SyntaxNodeKind := `selNegNum
meta def selAtomLitKind : SyntaxNodeKind := `selAtomLit
meta def selLeanKind : SyntaxNodeKind := `selLean

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
@[spytial_sel_parser] meta def sgqAtomLitRule : Parser :=
  leadingNode selAtomLitKind (Sgq.Construct.of .«atomLiteral»).prec nameLit
@[spytial_sel_parser] meta def sgqLetRule : Parser := ruleFor .«let»
/-- `lean (…)`: an ordinary Lean function read as a relation. The term needs
    Lean's own token table back, and the brackets are the grammar's own, which
    is what puts them in `selTokens`. -/
@[spytial_sel_parser] meta def sgqLeanRule : Parser :=
  let g := Sgq.Construct.of .«grouping»
  leadingNode selLeanKind atomPrec
    (spelledAs "lean" >> spelledAs (g.part .«open»).text >>
      withHostTokens termParser >> spelledAs (g.part .«close»).text)

/-! ## Elaboration -/

/-- `arity` is `none` when statically unknown, which disables width checks
    downstream. -/
meta structure EExpr where
  sel : Sel
  kind : Sgq.Kind
  arity : Option Nat := none
  deriving Inhabited

meta inductive LocalBind where
  | binder
  | letE (e : EExpr)

/-- Most-recent first; a later binder shadows an earlier `let` and vice versa. -/
meta abbrev LEnv := List (Name × LocalBind)

private meta def constructOfKind : Std.HashMap Name Sgq.ConstructId :=
  Sgq.allConstructs.foldl (init := {}) fun m c => m.insert (nodeKind c) c

/-- Atom constructs read off an identifier rather than a rule of their own. -/
private meta def wordConstructs : List Sgq.ConstructId :=
  Sgq.allConstructs.filter fun c =>
    let cd := Sgq.Construct.of c
    cd.evaluates && cd.fixity == .atom && !cd.operators.isEmpty

-- `resolveIdent` resolves a word to an operator without re-checking `evaluates`,
-- and constructs and operators carry their own: a bump that makes them disagree
-- here is the build's to catch, not an audit's.
open Command in
run_cmd
  for c in wordConstructs do
    let refused := (Sgq.Construct.of c).operators.filter fun o =>
      !(Sgq.Op.of o).evaluates
    unless refused.isEmpty do
      throwError "sgq manifest: the bare-word construct '{Sgq.constructName c}' \
        has operators the engine refuses to evaluate \
        ({", ".intercalate (refused.map Sgq.opName)}), and `resolveIdent` \
        resolves a word to one without checking"

private meta def kindName : Sgq.Kind → String
  | .relation => "a relational expression" | .number => "an integer expression"
  | .boolean => "a formula" | .«string» => "a label/literal value"
  | .operand => "an expression" | .any => "an expression"

private meta def kindAccepts (want : Option Sgq.Kind) (got : Sgq.Kind) : Bool :=
  match want with
  | none | some .any | some .operand => true
  | some k => k == got

private meta def yieldKind (declared : Option Sgq.Kind) (operands : Array Sgq.Kind) : Sgq.Kind :=
  match declared with
  | some .operand => operands[0]?.getD .relation
  | some k => k
  | none => .relation

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

/-- Aim at the owner type for a non-structure field: it has no projection. -/
private meta def addRelInfo (stx : Syntax) (owner : Name) (relName : String) :
    TermElabM Unit := do
  let env ← getEnv
  let proj := Name.mkStr owner relName
  let target := if env.contains proj then proj else owner
  if env.contains target then
    addConstInfo stx target

private meta def resolveCtorLit? (scope : SelScope) (stx : Syntax) : TermElabM (Option Sel) := do
  if let some ctorName := scope.ctorLabels.get? (stx.getId.toString (escape := false)) then
    if let some e ← try pure (some (← mkConstWithLevelParams ctorName)) catch _ => pure none then
      discard <| Term.addTermInfo stx e
    return some (.ctorLit ctorName)
  return none

private meta def builtinArity? (s : String) : Option Nat :=
  if Sgq.binaryBuiltins.contains s then some 2
  else if Sgq.unaryBuiltins.contains s then some 1
  else none

/-- Spellings are unique within a construct, so the `.operator` atom decides. -/
private meta def opWritten? (cd : Sgq.Construct) (stx : Syntax) : Option Sgq.OpId := do
  cd.operatorSpelled (stx[← cd.template.findIdx? (· matches .operator)].getAtomVal)

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

/-- A bare ident opposite a label projection (`@:x = tt`) is a constructor
    label, not a relation. The opposite operand's `declaredKind?` chooses this
    reading before this side elaborates, so the error names the right vocabulary. -/
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
    return { sel := .ctorLit constName, kind := .«string» }
  | _ =>
    throwErrorAt x m!"'{constName}' is not a constructor; label comparisons \
      expect a constructor or a literal"

private meta def elabLeanRel (scope : SelScope) (stx : TSyntax `term) :
    TermElabM EExpr := do
  let fn ← instantiateMVars (← Term.withSynthesize <| Term.elabTerm stx none)
  -- a written `sorry` reports nothing of its own, so name the consequence
  if fn.hasSorry then
    logWarningAt stx "this term carries a sorry, so the op selects nothing at \
      render"
    return { sel := .empty, kind := .relation }
  if fn.hasExprMVar || fn.hasLevelMVar then
    throwErrorAt stx "a Lean selector cannot contain unresolved holes"
  let kind ← withRef stx <| classifyLeanRel fn
  -- a predicate may capture local parameters and be established from evidence
  -- without a `Decidable` instance; a whole-value program still runs as code
  if let .sel _ := kind.shape then
    if fn.hasFVar then
      throwErrorAt stx "a whole-value Lean selector must be a closed term"
  unless scope.lenient do
    for col in kind.domains do
      if let some n ← typeHead? col then
        unless scope.types.contains n do
          logWarningAt stx m!"'{n}' is not among the types reachable from \
            '{scope.root}', so this selector cannot match anything"
  return { sel := .leanRel fn, kind := .relation, arity := some kind.arity }

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
    | some n => return { sel := .atomLit n.toString, kind := .relation, arity := some 1 }
    | none => throwErrorAt stx "malformed atom literal"
  else if k == selLeanKind then
    elabLeanRel scope ⟨stx[2]⟩
  else if k == nodeKind .«let» then
    elabLet scope env stx
  else match constructOfKind.get? k with
    | some c => elabNode scope env stx c
    | none => throwErrorAt stx "unexpected selector syntax"

private meta partial def elabNode (scope : SelScope) (env : LEnv) (stx : Syntax)
    (c : Sgq.ConstructId) : TermElabM EExpr := do
  let cd := Sgq.Construct.of c
  -- the renderer re-derives parentheses from the cascade
  if cd.kinds.yields == some .operand && cd.kinds.operands == [Option.some .operand] then
    if let some i := cd.template.findIdx? (· matches .operand _) then
      return ← elabExpr scope env stx[i]
  if cd.kinds.yields.isNone then
    if let some e ← elabBuiltinCall? scope env stx c then return e
  let op? := opWritten? cd stx
  let od? := op?.map Sgq.Op.of
  let kinds := (od?.map (·.kinds)).getD cd.kinds
  let arity := (od?.map (·.arity)).getD cd.arity
  let what : String := match od? with
    | some od => od.text
    | none => s!"a {Sgq.constructName c}"
  if let some od := od? then
    unless od.evaluates do
      throwErrorAt stx m!"the engine parses '{what}' and refuses to evaluate it"
  let mut args : Array Arg := #[]
  let mut slots : Array (Option Nat) := #[]
  let mut opKinds : Array Sgq.Kind := #[]
  let mut extra : Array (Option Nat) := #[]
  let mut binders : Nat := 0
  let mut env := env
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
    | .part _ opt =>
      if opt then
        let s := stx[i].getAtomVal
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
  if kinds.operands.any (· == Option.some .any) then
    for k in opKinds do
      unless k == opKinds[0]! do
        throwErrorAt stx m!"cannot compare {kindName opKinds[0]!} with {kindName k}"
  if arity.yields matches some .boxJoin && extra.isEmpty then
    throwErrorAt stx "box join needs at least one argument (`a[b]` means `b.a`)"
  let width ← applyArity stx what arity slots extra binders
  return { sel := .node c op? args, kind := yieldKind kinds.yields opKinds, arity := width }

/-- In an `any` slot, what the *other* slot yields decides how a bare ident reads. -/
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

/-- A bracket whose callee names a builtin is a call, not a box join. -/
private meta partial def elabBuiltinCall? (scope : SelScope) (env : LEnv) (stx : Syntax)
    (c : Sgq.ConstructId) : TermElabM (Option EExpr) := do
  let cd := Sgq.Construct.of c
  let some ci := cd.template.findIdx? (· matches .operand _) | return none
  let some li := cd.template.findIdx? (· matches .list _ _) | return none
  unless stx[ci].isOfKind selIdentKind do return none
  let callee := stx[ci][0]
  if (env.lookup callee.getId).isSome then return none
  let .ident _ raw _ _ := callee | return none
  let name := raw.toString
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
    -- aggregators read numeric values, but walker atom ids are opaque (`atom_N`)
    -- and the value is the label, so decode via the engine's own projection
    let proj := Sgq.Op.of .«labelNumber»
    let inner : Sel := .node proj.construct (some proj.id) #[.expr e.sel]
    return some { sel := .node c none #[.expr (.builtin name), .exprs #[inner]],
                  kind := .number }
  return none

/-- An `any` slot passes `none`: `elabNode` reconciles the operands instead. -/
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
      -- ours, not the engine's: it ranges a binder over the *atoms* of a wider
      -- domain, which is never what the source meant
      if let some a := dom.arity then
        unless a == 1 do
          throwErrorAt group[2] m!"a {what} binder domain must have arity 1, got {a}"
      for x in group[0].getSepArgs do
        binders := binders.push (x.getId, dom.sel)
        env := (x.getId, .binder) :: env
    else
      let e ← elabExpr scope env group[2]
      env := (group[0].getId, .letE e) :: env
      binders := binders.push (group[0].getId, e.sel)
  if binders.isEmpty then throwError s!"a {what} needs at least one binder"
  return (binders, env)

/-- SGQ has no `let`; it desugars by substitution at use. -/
private meta partial def elabLet (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM EExpr := do
  let (_, env') ← elabBinders scope env false "let" stx[1].getSepArgs
  elabExpr scope env' stx[2][1]

private meta partial def resolveIdent (scope : SelScope) (env : LEnv)
    (stx : TSyntax `ident) : TermElabM EExpr := do
  -- source text, not the name, decides: `«univ»` is a field spelled differently
  -- that parses to the same `Name`
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
  if let some i := scope.introduced.get? s then
    warnGraphSideName stx s
    return { sel := .rel s, kind := .relation, arity := some i.arity }
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

/-- `blockedBy` names a field the form needs and the op did not write: the form
    is unavailable, and only the diagnostic reads it, to say what unlocks the
    width. -/
meta structure ArityForm where
  min : Nat
  max : Option Nat
  blockedBy : Option String := none
  /-- The engine keeps only the first and last column of a tuple this wide. -/
  middlesIgnored : Bool := false
  deriving Repr, Inhabited

meta def ArityForm.holds (f : ArityForm) (a : Nat) : Bool :=
  f.min ≤ a && f.max.all (a ≤ ·)

private meta def mergeRanges (forms : List ArityForm) : Array (Nat × Option Nat) :=
  (forms.toArray.qsort (·.min < ·.min)).foldl (init := #[]) fun acc f =>
    match acc.back? with
    | some (_, none) => acc
    | some (lo, some hi) =>
      if f.min ≤ hi + 1 then acc.set! (acc.size - 1) (lo, f.max.map (Nat.max hi))
      else acc.push (f.min, f.max)
    | none => acc.push (f.min, f.max)

private meta def widthPhrase (forms : List ArityForm) : String :=
  " or ".intercalate <| (mergeRanges forms).toList.map fun
    | (lo, some hi) => if lo == hi then toString lo else s!"{lo} to {hi}"
    | (lo, none) => s!"{lo} or wider"

meta def elabSelector (scope : SelScope) (accepts : List ArityForm)
    (stx : TSyntax `spytial_sel) : TermElabM Sel := do
  let e ← elabExpr scope [] stx
  unless e.kind == .relation do
    throwErrorAt stx m!"a selector picks out atoms or tuples, but this is \
      {kindName e.kind}"
  if let some a := e.arity then
    let (available, blocked) := accepts.partition (·.blockedBy.isNone)
    let matching := available.filter (·.holds a)
    if matching.isEmpty then
      let unlock := (blocked.filter (·.holds a)).filterMap (·.blockedBy)
      throwErrorAt stx m!"this position accepts a selector of arity \
        {widthPhrase available}, but this one has arity {a}\
        {if unlock.isEmpty then m!"" else
          m!"; arity {a} needs {" or ".intercalate (unlock.map (s!"'{·}'"))}"}"
    -- only where every form that takes this width discards the middles: a
    -- position that shows them (`inferredEdge`, `tag`) is not losing anything
    else if 2 < a && matching.all (·.middlesIgnored) then
      logWarningAt stx m!"arity-{a} selector: this position uses only the first \
        and last columns of each tuple"
  return e.sel

/-- `position` is the `<item>.<field>` the name sits in: a spec-introduced name
    is resolved only where the manifest says it is. -/
meta def elabFieldName (scope : SelScope) (position : String) (stx : TSyntax `ident) :
    TermElabM String := do
  let s := stx.getId.toString (escape := false)
  if scope.rels.contains s then
    return s
  if let some i := scope.introduced.get? s then
    unless i.referencedBy.contains position do
      warnUnresolvedName stx position s
    return s
  unknownName scope stx s!"relation '{s}'" s

end

end SpytialLean

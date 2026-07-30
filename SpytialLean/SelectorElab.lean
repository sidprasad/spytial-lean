module

public import Lean
public meta import SpytialLean.Selector
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Elab Meta

public section

/-! # SelectorElab — embedded selector syntax, checked against the data vocabulary

Selectors are written as Lean syntax (categories `spytial_sel` and
`spytial_sel_form`) and elaborated against a `SelScope`: the vocabulary of atoms
and relations the relationalizer can emit for values of the target type. Every
identifier must resolve — to a comprehension/quantifier binder, a `let`-binding,
a field relation, a type in the reachable closure, or (in value position) a
nullary constructor — and every operator's arity and type must make sense, so a
renamed cslib field or a typo'd sig is a compile error at the exact ident, not a
silently empty selection at render time.

The surface grammar mirrors Forge's expression/formula cascade. `spytial_sel`
carries a small typed sub-language: an expression elaborates to one of three
kinds (`EExpr`) — a relational value, a label/string/bool value, or an integer —
and each position accepts exactly the kinds that make sense. This statically
rules out SGQ's silent scalar/tuple confusion (e.g. `some #e` evaluates to false
with no error; here it is a type error).

Scopes are *strict* exactly when the vocabulary is closed: a monomorphic type
built from monomorphic fields. A type parameter, function-typed field, custom
relationalizer, or non-inductive in the closure opens the world — the walker can
then emit names no static analysis predicts — and unknown names downgrade to
warnings there.
-/

/-! ## Scope -/

/-- The statically-known data vocabulary of a target type: everything the
    relationalizer can emit for values of that type, per `TypeShape`. -/
meta structure SelScope where
  root : Name
  /-- Lean type name → sig string, over the reachable field-type closure. -/
  types : Std.HashMap Name String := {}
  /-- Relation name → the type whose constructor field emits it. Proof-like
      fields (`Prop`- or `Sort`-typed) are excluded — the walker drops them. -/
  rels : Std.HashMap String Name := {}
  /-- Nullary-constructor label → constructor, for `@:x = tt` literals. -/
  ctorLabels : Std.HashMap String Name := {}
  /-- Names introduced by earlier ops in the same spec (group names arity 1,
      inferred edges arity 2). -/
  introduced : Std.HashMap String Nat := {}
  /-- Open-world marker (see module docstring): unknown names become warnings. -/
  lenient : Bool := false
  deriving Inhabited

/-- Types whose values the walker renders as literal atoms rather than
    constructor trees — their constructors and fields are not vocabulary. -/
private meta def scalarTypes : List Name :=
  [``Nat, ``Int, ``String, ``Char, ``Float, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize]

/-- Compute the scope of `root`: walk the field-type closure collecting sigs,
    relation names, and nullary-constructor labels. `seeds` adds extra starting
    points — the root type's own type arguments, when the caller has them
    (`List Node` contributes `Node`). -/
meta def SelScope.ofType (root : Name) (seeds : Array Name := #[]) : MetaM SelScope := do
  let env ← getEnv
  let mut scope : SelScope := { root }
  -- Stuck-match nodes can appear in any open value, typed at the scrutinized type.
  scope := { scope with rels := scope.rels.insert "scrutinee" root }
  let mut queue : Array Name := #[root] ++ seeds
  let mut seen : NameSet := {}
  while !queue.isEmpty do
    let t := queue.back!
    queue := queue.pop
    if seen.contains t then continue
    seen := seen.insert t
    scope := { scope with types := scope.types.insert t (shortName t) }
    -- A custom relationalizer replaces the default walk for this type: its
    -- emissions are its own, so the world is open past this point.
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
        if c.fields.isEmpty then
          scope := { scope with ctorLabels := scope.ctorLabels.insert c.ctorShort c.ctorName }
        for f in c.fields do
          -- Proof-like fields are dropped by the walker, so they neither add
          -- vocabulary nor (via an unresolved head) open the world.
          unless f.isProofLike do
            scope := { scope with rels := scope.rels.insert f.relName t }
            match f.typeHead with
            | some ft => queue := queue.push ft
            | none => scope := { scope with lenient := true }
            queue := queue ++ f.typeArgHeads
  return scope

/-- Register a spec-introduced name (a group, an inferred edge) with its arity. -/
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

/-- The names a bare identifier could have meant, for error messages. -/
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

/-- `U+`-prefixed hexadecimal spelling of a character, for naming one that has
    no printable form in a diagnostic. -/
private meta def codepoint (c : Char) : String :=
  s!"U+{String.ofList ((Nat.toDigits 16 c.val.toNat).leftpad 4 '0') |>.toUpper}"

/-- Unknown-name handling: an error in strict scopes, a warning in lenient ones
    (the walker may legitimately emit names we cannot predict there). Returns
    the recovery value used when lenient. -/
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

/-! ## Syntax

The grammar replicates Forge's single expression/formula cascade over two Lean
categories, both `behavior := both` so keyword-led rules and bare identifiers
coexist — a relation literally named `some` still parses, and the syntax
elaborator compiles each leading keyword to a `nonReservedSymbol`. Multiplicity/
quantifier forms with a mandatory further token win by longest-match; the nullary
constants (`univ`/`iden`/`none`) tie with a bare ident on span, so they take
`priority := high` to pick the constant. The precedence numbers below are Forge's
cascade re-scaled: loosest at the top. -/

open Lean Parser

-- Both categories are `behavior := both`. The catch: under non-default behavior
-- the `syntax` sugar rewrites a rule's first atom to `nonReservedSymbol`, which
-- registers no token — so `@:`/`@str:`/`@bool:`/`@num:` would maximal-munch onto
-- the global `@`. The `@`-family is therefore hand-written below with a reserved
-- `symbol` head (which does register the token).
declare_syntax_cat spytial_sel (behavior := both)
declare_syntax_cat spytial_sel_form (behavior := both)

/-- Binder group of a comprehension or quantifier: `x, y : BDD`. -/
syntax spytialSelBinderGroup := sepBy1(ident, ", ") " : " spytial_sel

/-! ### Relational / integer expressions (`spytial_sel`), loosest → tightest -/

syntax:30 spytial_sel:30 " + " spytial_sel:31 : spytial_sel
syntax:30 spytial_sel:30 " - " spytial_sel:31 : spytial_sel
-- `#` cardinality (Forge Expr9): tighter than `+`/`-`, looser than the rest.
syntax:34 (name := selCard) "#" spytial_sel:35 : spytial_sel
syntax:36 spytial_sel:36 " ++ " spytial_sel:37 : spytial_sel
syntax:40 spytial_sel:40 " & " spytial_sel:41 : spytial_sel
-- Product `A -> B` (prec 50) is the hand-written `selProdOp` below, so its
-- arrow-multiplicity annotations stay non-reserving.
syntax:55 spytial_sel:55 " <: " spytial_sel:56 : spytial_sel
syntax:55 spytial_sel:55 " :> " spytial_sel:56 : spytial_sel
syntax:60 spytial_sel:60 " . " spytial_sel:61 : spytial_sel
syntax:60 (name := selBox) spytial_sel:60 noWs "[" sepBy(spytial_sel, ", ") "]" : spytial_sel
syntax:70 "^" spytial_sel:70 : spytial_sel
syntax:70 "*" spytial_sel:70 : spytial_sel
syntax:70 "~" spytial_sel:70 : spytial_sel
-- Label projections (SGQ extension; Forge has no `@`): expr-tier prefix ops,
-- hand-written with reserved `symbol` heads so the token registers under `.both`
-- (see the note above the category). Dispatched by kind in `elabExpr` — the same
-- kinds `elabCmp` classifies, so kind dispatch is the single mechanism.
@[spytial_sel_parser] meta def selProjPlainOp : Parser :=
  leadingNode `selProjPlain 100 (symbol "@:" >> categoryParser `spytial_sel 100)
@[spytial_sel_parser] meta def selProjStrOp : Parser :=
  leadingNode `selProjStr 100 (symbol "@str:" >> categoryParser `spytial_sel 100)
@[spytial_sel_parser] meta def selProjBoolOp : Parser :=
  leadingNode `selProjBool 100 (symbol "@bool:" >> categoryParser `spytial_sel 100)
@[spytial_sel_parser] meta def selProjNumOp : Parser :=
  leadingNode `selProjNum 100 (symbol "@num:" >> categoryParser `spytial_sel 100)
syntax:100 (name := selIdent) ident : spytial_sel
syntax:100 "(" spytial_sel ")" : spytial_sel
syntax:100 "{" sepBy1(spytialSelBinderGroup, ", ") " | " spytial_sel_form "}" : spytial_sel
-- Escape hatch: a string literal in a *whole-selector* position is a verbatim,
-- unchecked SGQ expression (for genuinely dynamic-vocabulary queries the checker
-- cannot know); nested in a comparison it is an ordinary string literal.
syntax:100 (name := selStr) str : spytial_sel
syntax:100 (name := selNum) num : spytial_sel
syntax:100 (name := selNegNum) "-" noWs num : spytial_sel
/-- Backquote atom literal (`` `a0 ``). Lean's `name` literal is the faithful
    spelling; a bare backtick atom is rejected by the syntax elaborator. -/
syntax:100 (name := selAtomLit) name : spytial_sel

-- Forge constants (Expr18): real non-reserving keyword rules. `priority := high`
-- breaks the same-span longest-match tie with `selIdent` (a bare nullary keyword
-- and a bare ident each span one token), picking the constant; a field literally
-- named `univ` stays reachable via the glued join `x.univ` (one ident token the
-- keyword never matches).
syntax:100 (name := selUniv) (priority := high) "univ" : spytial_sel
syntax:100 (name := selIden) (priority := high) "iden" : spytial_sel
syntax:100 (name := selNone) (priority := high) "none" : spytial_sel

-- `sum x : A | ie` (Forge Expr0): the integer aggregation quantifier. Single
-- binder (Forge's expander gives `sum` no comma-groups, unlike the boolean
-- quantifiers); the body is an integer expression and the whole form is an
-- integer. No priority needed — bare `sum` fails the rule (no binder follows) and
-- falls to `selIdent`, so a field named `sum` still parses.
syntax:5 (name := selSum) "sum " ident " : " spytial_sel " | " spytial_sel : spytial_sel

/-- One optional arrow-multiplicity keyword, non-reserving. -/
private meta def arrowMultP : Parser :=
  nonReservedSymbol "lone" (includeIdent := true) <|>
    nonReservedSymbol "one" (includeIdent := true) <|>
    nonReservedSymbol "some" (includeIdent := true) <|>
    nonReservedSymbol "set" (includeIdent := true)

/-- Arrow-multiplicity product (`A one -> lone B`), replacing the plain `->` rule.
    Both annotations are optional. `includeIdent` lets a left annotation trigger
    the trailing parser; the right side is `atomic` over `mult >> operand` so a
    relation literally named `one`/`lone`/… stays usable as the bare right
    operand (it falls through to `pushNone >> operand`). The node always has the
    shape `[lhs, leftOpt, "->", rightMultOrNull, rhs]`. -/
@[spytial_sel_parser] meta def selProdOp : TrailingParser :=
  trailingNode `selProd 50 50
    (Lean.Parser.optional arrowMultP >> symbol "->" >>
      ((Lean.Parser.atomic (arrowMultP >> categoryParser `spytial_sel 51)) <|>
        (Lean.Parser.pushNone >> categoryParser `spytial_sel 51)))

/-! ### Formulas (`spytial_sel_form`), loosest → tightest -/

-- Quantified formulas (Forge Expr0): `Q disj? binders | φ`. `some/no/lone/one`
-- also lead multiplicity formulas below; longest-match picks this binder form.
syntax:5 (name := selQAll)  "all "  (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form
syntax:5 (name := selQNo)   "no "   (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form
syntax:5 (name := selQSome) "some " (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form
syntax:5 (name := selQLone) "lone " (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form
syntax:5 (name := selQOne)  "one "  (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form

-- `let x = e, … | φ` — desugared at elaboration by substitution (SGQ has no let).
syntax:5 (name := selLet) "let " sepBy1(ident " = " spytial_sel, ", ") " | " spytial_sel_form:5 : spytial_sel_form

-- Comparisons (Forge Expr6). Relational: `in = != ni`; negated subset `!in`;
-- int-only: `< > <= >= =<` (`=<` is a Forge alias for `<=`).
syntax:50 spytial_sel " = "   spytial_sel : spytial_sel_form
syntax:50 spytial_sel " != "  spytial_sel : spytial_sel_form
syntax:50 spytial_sel " in "  spytial_sel : spytial_sel_form
-- `!in` must be the two existing tokens `!` `in`: a dedicated `"!in"` atom
-- would enter the global token table and maximal-munch would steal the prefix
-- of ordinary negations like `!input` in every importing module.
syntax:50 spytial_sel " !" "in " spytial_sel : spytial_sel_form
syntax:50 spytial_sel " < "   spytial_sel : spytial_sel_form
syntax:50 spytial_sel " > "   spytial_sel : spytial_sel_form
syntax:50 spytial_sel " <= "  spytial_sel : spytial_sel_form
syntax:50 spytial_sel " >= "  spytial_sel : spytial_sel_form
syntax:50 spytial_sel " =< "  spytial_sel : spytial_sel_form

-- `a not in b`, `a ni b`, and negated `a !ni b` / `a not ni b` — `not`/`ni` are
-- non-reserving interior keywords, so these are hand-written rather than `syntax`
-- rules (which would reserve the words, breaking any importer's ident named `ni`
-- etc.); `!` is an existing token.
@[spytial_sel_form_parser] meta def selNotInOp : Parser :=
  leadingNode `selNotIn 50
    (categoryParser `spytial_sel 0 >> nonReservedSymbol "not" >> symbol "in" >>
      categoryParser `spytial_sel 0)

@[spytial_sel_form_parser] meta def selNiOp : Parser :=
  leadingNode `selNi 50
    (categoryParser `spytial_sel 0 >> nonReservedSymbol "ni" >>
      categoryParser `spytial_sel 0)

@[spytial_sel_form_parser] meta def selNotNiOp : Parser :=
  leadingNode `selNotNi 50
    (categoryParser `spytial_sel 0 >> (symbol "!" <|> nonReservedSymbol "not") >>
      nonReservedSymbol "ni" >> categoryParser `spytial_sel 0)

-- Multiplicity formulas (Forge Expr7 applies to Expr8): `some/no/lone/one <sel>`.
-- The operand grabs a full expression (down to union) so `some A + B` is
-- `some (A + B)`.
syntax:60 "some " spytial_sel:30 : spytial_sel_form
syntax:60 "no "   spytial_sel:30 : spytial_sel_form
syntax:60 "lone " spytial_sel:30 : spytial_sel_form
syntax:60 "one "  spytial_sel:30 : spytial_sel_form

-- Negation (Forge Expr5). Word form is a leading sugar rule (`.both` makes it
-- non-reserving); symbolic form uses the existing `!` token.
syntax:40 "! "  spytial_sel_form:40 : spytial_sel_form
syntax:40 "not " spytial_sel_form:40 : spytial_sel_form

syntax:100 "(" spytial_sel_form ")" : spytial_sel_form

/-- A binary formula connective accepting either spelling. Trailing so the
    behavior-blind trailing loop reaches the word form via `identKind`. -/
private meta def connOp (kind : SyntaxNodeKind) (prec lhsPrec rhsPrec : Nat) (opP : Parser) :
    TrailingParser :=
  trailingNode kind prec lhsPrec (opP >> categoryParser `spytial_sel_form rhsPrec)

-- `includeIdent` indexes the word spelling under `identKind`, so the
-- behavior-blind trailing loop reaches it after any formula.
private meta def wordSym (sym word : String) : Parser :=
  symbol sym <|> nonReservedSymbol word (includeIdent := true)

-- Connective tiers (loosest → tightest): or < xor < iff < implies < and.
-- `implies` is right-associative (rhs at its own precedence); the rest left.
@[spytial_sel_form_parser] meta def selOrOp   : TrailingParser := connOp `selOr   10 10 11 (wordSym "||" "or")
@[spytial_sel_form_parser] meta def selXorOp  : TrailingParser := connOp `selXor  13 13 14 (nonReservedSymbol "xor" (includeIdent := true))
@[spytial_sel_form_parser] meta def selIffOp  : TrailingParser := connOp `selIff  16 16 17 (wordSym "<=>" "iff")
@[spytial_sel_form_parser] meta def selImpOp  : TrailingParser := connOp `selImplies 20 21 20 (wordSym "=>" "implies")
@[spytial_sel_form_parser] meta def selAndOp  : TrailingParser := connOp `selAnd  30 30 31 (wordSym "&&" "and")

-- Formula-level if-then-else: `c implies t else e` (right-associative in `e`).
@[spytial_sel_form_parser] meta def selIteOp : TrailingParser :=
  trailingNode `selIte 20 21
    (wordSym "=>" "implies" >> categoryParser `spytial_sel_form 21 >>
      symbol "else" >> categoryParser `spytial_sel_form 20)

/-! ## Elaboration

Elaboration classifies each expression into an `EExpr` — relational, label/value,
or integer — and each position accepts exactly the kinds it can use. Relational
results carry an arity (`none` = statically unknown: `raw`, or a leniently-passed
unknown name), which soft-disables downstream arity requirements. -/

/-- The typed result of elaborating a `spytial_sel`. Compile-time only — never
    stored, so it needs no `Repr`/pickling. -/
meta inductive EExpr where
  | rel (s : Sel) (arity : Option Nat)
  | val (v : SelVal)
  | int (i : SelInt)

/-- A local binding introduced by a comprehension/quantifier binder or a `let`. -/
meta inductive LocalBind where
  | binder                 -- ranges over a domain (arity 1)
  | letE (e : EExpr)       -- `let`-bound: substituted at use

/-- Ordered local environment (most-recent first); a later binder shadows an
    earlier `let` of the same name and vice versa. -/
meta abbrev LEnv := List (Name × LocalBind)

private meta def checkArity (ref : Syntax) (what : String) (got : Option Nat)
    (want : Nat) : TermElabM Unit := do
  if let some got := got then
    unless got == want do
      throwErrorAt ref m!"{what} must have arity {want}, got {got}"

private meta def joinArity (ref : Syntax) : Option Nat → Option Nat → TermElabM (Option Nat)
  | some a, some b => do
    if a + b < 3 then
      throwErrorAt ref m!"join of arity {a} and arity {b} has no columns left"
    return some (a + b - 2)
  | _, _ => return none

private meta def sameArity (ref : Syntax) (op : String) :
    Option Nat → Option Nat → TermElabM (Option Nat)
  | some a, some b => do
    unless a == b do
      throwErrorAt ref m!"operands of {op} must have equal arity, got {a} and {b}"
    return some a
  | some a, none | none, some a => return some a
  | none, none => return none

/-- Resolve an ident as a global constant, quietly returning `none` when it
    does not resolve (with hover/go-to-def info when it does). -/
private meta def resolveGlobal? (stx : Syntax) : TermElabM (Option Name) := do
  try
    pure (some (← realizeGlobalConstNoOverloadWithInfo stx))
  catch _ =>
    pure none

private meta def intBuiltinOf? : String → Option IntBuiltin
  | "add" => some .add | "subtract" => some .subtract | "multiply" => some .multiply
  | "divide" => some .divide | "remainder" => some .remainder
  | "abs" => some .abs | "sign" => some .sign | _ => none

private meta def IntBuiltin.arity : IntBuiltin → Nat
  | .abs | .sign => 1
  | _ => 2

private meta def intAggOf? : String → Option IntAgg
  | "sum" => some .sum | "min" => some .min | "max" => some .max | _ => none

/-- The nullary-constructor label a bare ident denotes, if it names one of the
    scope's constructors (`@:x = nil`): resolves the constructor (hover works)
    and lowers to the short-name label the relationalizer emits. -/
private meta def resolveCtorLit? (scope : SelScope) (stx : Syntax) : TermElabM (Option SelVal) := do
  if let some ctorName := scope.ctorLabels.get? stx.getId.toString then
    if let some e ← try pure (some (← mkConstWithLevelParams ctorName)) catch _ => pure none then
      discard <| Term.addTermInfo stx e
    return some (.ctorLit ctorName (shortName ctorName))
  return none

mutual

/-- Elaborate a `spytial_sel` into its typed kind. -/
private meta partial def elabExpr (scope : SelScope) (env : LEnv) :
    Syntax → TermElabM EExpr
  | `(spytial_sel| $x:ident) => resolveExprIdent scope env x
  | `(spytial_sel| ($s)) => elabExpr scope env s
  | `(spytial_sel| $s:str) => do
    if let some c := sgqUnspellableChar? s.getString then
      throwErrorAt s m!"string literal contains {codepoint c} — SGQ's string \
        syntax has no escape for it, and it cannot ride raw through the spec"
    return .val (.strLit s.getString)
  | `(spytial_sel| $n:num) => return .int (.lit (Int.ofNat n.getNat))
  | `(spytial_sel| -$n:num) => return .int (.lit (-(Int.ofNat n.getNat)))
  | `(spytial_sel| univ) => return .rel .univ (some 1)
  | `(spytial_sel| iden) => return .rel .iden (some 2)
  | `(spytial_sel| none) => return .rel .none_ (some 1)
  | `(spytial_sel| sum $x:ident : $dom | $body) => do
    let (domSel, domArity) ← elabRel scope env dom
    checkArity dom "a sum-quantifier binder domain" domArity 1
    let bodyInt ← elabInt scope ((x.getId, .binder) :: env) body
    return .int (.sumQuant x.getId domSel bodyInt)
  | `(spytial_sel| $a + $b) => elabRelBinary scope env .union "+" a b
  | `(spytial_sel| $a - $b) => elabRelBinary scope env .diff "-" a b
  | `(spytial_sel| $a & $b) => elabRelBinary scope env .inter "&" a b
  | stx@`(spytial_sel| $a ++ $b) => do
    logWarningAt stx "the SGQ engine currently throws on `++` (override) at \
      render — in a constraint position this kills the render (upstream bug)"
    let (sa, aa) ← elabRel scope env a
    let (sb, ab) ← elabRel scope env b
    return .rel (.override sa sb) (← sameArity stx "++" aa ab)
  | stx@`(spytial_sel| $a <: $b) => do
    logWarningAt stx "the SGQ engine currently throws on `<:` (domain restriction) \
      at render — in a constraint position this kills the render (upstream bug)"
    let (sa, _) ← elabRel scope env a
    let (sb, ab) ← elabRel scope env b
    return .rel (.restrictDom sa sb) ab
  | stx@`(spytial_sel| $a :> $b) => do
    logWarningAt stx "the SGQ engine currently throws on `:>` (range restriction) \
      at render — in a constraint position this kills the render (upstream bug)"
    let (sa, aa) ← elabRel scope env a
    let (sb, _) ← elabRel scope env b
    return .rel (.restrictRan sa sb) aa
  | stx@`(spytial_sel| $a . $b) => do
    let (sa, aa) ← elabRel scope env a
    let (sb, ab) ← elabRel scope env b
    return .rel (.join sa sb) (← joinArity stx aa ab)
  | stx@`(spytial_sel| ^$a) => elabClosure scope env stx .trans "^" a
  | stx@`(spytial_sel| *$a) => elabClosure scope env stx .reflTrans "*" a
  | stx@`(spytial_sel| ~$a) => elabClosure scope env stx .transpose "~" a
  | stx@`(spytial_sel| #$a) => do
    let (sa, _) ← elabRel scope env a
    return .int (.card sa)
  | stx@`(spytial_sel| $a:name) => do
    logWarningAt stx "the SGQ engine does not evaluate backquote atom literals — \
      it renders an `UNIMPLEMENTED` placeholder (upstream bug)"
    match a.raw.isNameLit? with
    | some n => return .rel (.atomLit n.toString) (some 1)
    | none => throwErrorAt stx "malformed atom literal"
  | `(spytial_sel| {$groups,* | $body}) => do
    let (binders, env') ← elabBinderGroups scope env "comprehension" (groups.getElems.map (·.raw))
    let bodyForm ← elabForm scope env' body
    return .rel (.compr binders bodyForm) (some binders.size)
  | stx => do
    let k := stx.getKind
    -- Label projections, matched by kind (the same kinds `elabCmp` classifies).
    if k == `selProjPlain then return .val (← elabLabel scope env .plain ⟨stx[1]⟩)
    else if k == `selProjStr then return .val (← elabLabel scope env .str ⟨stx[1]⟩)
    else if k == `selProjBool then return .val (← elabLabel scope env .bool ⟨stx[1]⟩)
    else if k == `selProjNum then do
      let (sel, arity) ← elabRel scope env stx[1]
      checkArity stx[1] "a label projection's operand" arity 1
      return .int (.proj sel)
    else if k == `selProd then elabProd scope env stx  -- hand-written kind
    else elabBoxJoin? scope env stx

/-- Box join `e[a, …]`: dispatch to an integer builtin/aggregator when the head
    is one of their names, else a relational join (`e[a] ≡ a.e`). -/
private meta partial def elabBoxJoin? (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM EExpr := do
  match stx with
  | `(spytial_sel| $head[$args,*]) => do
    let argSyns := args.getElems
    let headName? : Option String := match head with
      | `(spytial_sel| $x:ident) =>
        if (env.lookup x.getId).isSome then none else some x.getId.toString
      | _ => none
    match headName? with
    | some hn =>
      if let some op := intBuiltinOf? hn then
        unless argSyns.size == op.arity do
          throwErrorAt stx m!"'{hn}' takes {op.arity} integer argument(s), got {argSyns.size}"
        let iargs ← argSyns.mapM (elabInt scope env)
        return .int (.builtin op iargs)
      if let some op := intAggOf? hn then
        unless argSyns.size == 1 do
          throwErrorAt stx m!"'{hn}[e]' takes one relational argument, got {argSyns.size}"
        let (sa, aa) ← elabRel scope env argSyns[0]!
        -- Aggregators fold a single column of integers (arity 1).
        checkArity argSyns[0]! s!"the argument of {hn}[e]" aa 1
        if op == .sum then
          logWarningAt stx "the SGQ engine evaluates `sum[e]` to the empty set \
            rather than summing its atoms (upstream bug)"
        return .int (.agg op sa)
      elabRelBoxJoin scope env stx head argSyns
    | none => elabRelBoxJoin scope env stx head argSyns
  | _ => throwErrorAt stx "unexpected selector syntax"

/-- A relational box join `e[a, b] ≡ b.a.e` (each argument joins on the left). -/
private meta partial def elabRelBoxJoin (scope : SelScope) (env : LEnv) (stx : Syntax)
    (head : Syntax) (args : Array Syntax) : TermElabM EExpr := do
  if args.isEmpty then
    throwErrorAt stx "box join needs at least one argument (`a[b]` means `b.a`)"
  let (hs, ha) ← elabRel scope env head
  let mut sel := hs
  let mut arity := ha
  for arg in args do
    let (asel, aar) ← elabRel scope env arg
    arity ← joinArity stx aar arity
    sel := .join asel sel
  return .rel sel arity

/-- The arrow-mult product node `selProd`, shaped `[lhs, leftOpt, "->",
    rightMultOrNull, rhs]` (see `selProdOp`). -/
private meta partial def elabProd (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM EExpr := do
  let lm := if stx[1].getNumArgs == 0 then none else arrowMultOf? stx[1][0]
  let rm := arrowMultOf? stx[3]
  let (sa, aa) ← elabRel scope env stx[0]
  let (sb, ab) ← elabRel scope env stx[4]
  let arity : Option Nat := do return (← aa) + (← ab)
  if lm.isSome || rm.isSome then
    logWarningAt stx "the SGQ engine silently drops arrow-multiplicity \
      annotations — `A one -> lone B` evaluates as the plain product `A -> B` \
      (upstream bug)"
    return .rel (.prodMult sa lm rm sb) arity
  return .rel (.prod sa sb) arity
where
  arrowMultOf? (s : Syntax) : Option ArrowMult :=
    match s.getAtomVal with
    | "lone" => some .lone | "one" => some .one
    | "some" => some .some | "set" => some .set | _ => none

/-- Elaborate `groups` (comma-separated binder groups) extending `env`. Each
    binder domain must be relational, arity 1. -/
private meta partial def elabBinderGroups (scope : SelScope) (env : LEnv)
    (what : String) (groups : Array Syntax) : TermElabM (Array (Name × Sel) × LEnv) := do
  let mut binders : Array (Name × Sel) := #[]
  let mut env := env
  for group in groups do
    match group with
    | `(spytialSelBinderGroup| $xs,* : $dom) => do
      let (domSel, domArity) ← elabRel scope env dom
      checkArity dom s!"a {what} binder domain" domArity 1
      for x in xs.getElems do
        binders := binders.push (x.getId, domSel)
        env := (x.getId, .binder) :: env
    | g => throwErrorAt g "unexpected binder group"
  return (binders, env)

/-- Require an expression to be relational; project its `Sel` and arity. -/
private meta partial def elabRel (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM (Sel × Option Nat) := do
  match ← elabExpr scope env stx with
  | .rel s a => return (s, a)
  | .int _ => throwErrorAt stx "this position expects a relational expression, \
      but the selector is an integer (`#`, a numeral, `@num:`, or an int builtin)"
  | .val _ => throwErrorAt stx "this position expects a relational expression, \
      but the selector is a label/literal value"

/-- Require an expression to be integer-typed. -/
private meta partial def elabInt (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM SelInt := do
  match ← elabExpr scope env stx with
  | .int i => return i
  | _ => throwErrorAt stx "this position expects an integer expression (`#e`, a \
      numeral, `@num:e`, or an int builtin)"

private meta partial def elabRelBinary (scope : SelScope) (env : LEnv)
    (mk : Sel → Sel → Sel) (op : String) (a b : TSyntax `spytial_sel) :
    TermElabM EExpr := do
  let (sa, aa) ← elabRel scope env a
  let (sb, ab) ← elabRel scope env b
  return .rel (mk sa sb) (← sameArity a op aa ab)

private meta partial def elabClosure (scope : SelScope) (env : LEnv) (stx : Syntax)
    (mk : Sel → Sel) (op : String) (a : TSyntax `spytial_sel) : TermElabM EExpr := do
  let (sa, aa) ← elabRel scope env a
  checkArity stx s!"the operand of {op}" aa 2
  return .rel (mk sa) (some 2)

private meta partial def elabLabel (scope : SelScope) (env : LEnv)
    (proj : LabelProj) (e : TSyntax `spytial_sel) : TermElabM SelVal := do
  let (sel, arity) ← elabRel scope env e
  checkArity e "a label projection's operand" arity 1
  return .label proj sel

/-- Resolve an identifier in expression position. A `let`-binding or binder wins
    first; a lone nullary-constructor ident is a label literal; multi-component
    idents (`x.v`) are join chains — unless the whole name resolves as a type. -/
private meta partial def resolveExprIdent (scope : SelScope) (env : LEnv)
    (stx : TSyntax `ident) : TermElabM EExpr := do
  match stx.getId.components with
  | [] => throwErrorAt stx "empty selector name"
  | head :: rest =>
    -- Local bindings (let / binder) take precedence over the vocabulary.
    if let some bind := env.lookup head then
      match bind with
      | .binder => return ← joinRest (.var head) (some 1) rest
      | .letE e =>
        -- Lowering is name-based, so a binder introduced after the `let` would
        -- silently capture the substituted expression's free variables.
        let fvs := match e with
          | .rel s _ => s.freeVars
          | .val v => v.freeVars
          | .int i => i.freeVars
        for (n, b) in env do
          if n == head then break
          if b matches .binder then
            if fvs.contains n then
              throwErrorAt stx m!"cannot use let-bound '{head}' here: it refers \
                to '{n}', which a nearer binder shadows — the substitution would \
                be captured; rename the inner binder"
        if rest.isEmpty then return e
        match e with
        | .rel s a => return ← joinRest s a rest
        | _ => throwErrorAt stx m!"'{head}' is a let-bound \
            {if let .int _ := e then "integer" else "value"}; it has no fields to join"
    if rest.isEmpty then
      -- A lone ident may be a nullary-constructor label (a value).
      if let some v ← resolveCtorLit? scope stx then
        return .val v
    let (sel, arity, unconsumed) ← resolveHead stx head rest
    joinRest sel arity unconsumed
where
  joinRest (sel : Sel) (arity : Option Nat) (rest : List Name) : TermElabM EExpr := do
    let s ← rest.foldlM (init := (sel, arity)) fun (sel, arity) comp => do
      let compStr := comp.toString
      -- Look up the component's real arity (rels first, mirroring `resolveHead`)
      -- rather than assuming a binary relation: a spec-introduced group is arity
      -- 1, so a join through it must be scored as such.
      let compArity? : Option Nat :=
        if scope.rels.contains compStr then some 2
        else scope.introduced.get? compStr
      match compArity? with
      | some ca => return (.join sel (.rel compStr), ← joinArity stx arity (some ca))
      | none => unknownName scope stx s!"relation '{compStr}'" (Sel.join sel (.rel compStr), none)
    return .rel s.1 s.2
  resolveHead (idStx : Syntax) (head : Name) (rest : List Name) :
      TermElabM (Sel × Option Nat × List Name) := do
    let s := head.toString
    if scope.rels.contains s then return (.rel s, some 2, rest)
    if let some arity := scope.introduced.get? s then return (.rel s, some arity, rest)
    -- Longest-prefix-as-reference: a dotted name may name a (possibly qualified)
    -- type in its leading components (`Cslib.SKI`, `SelQual.Inner`), the trailing
    -- components folding as joins. Try the full name first, then successively
    -- shorter prefixes down to the head; the first inductive hit is the
    -- reference, and its unconsumed tail is returned for `joinRest` to fold. A
    -- constructor hit errors inside `resolveTypeRef?` (label-comparison-only).
    let total := rest.length + 1
    for i in [0:total] do
      let prefixName := Nat.repeat Name.getPrefix i idStx.getId
      if let some (sel, arity) ← resolveTypeRef? (mkIdentFrom idStx prefixName) then
        return (sel, arity, rest.drop (total - 1 - i))
    unknownName scope idStx s!"name '{s}'" (Sel.rel s, none, rest)
  resolveTypeRef? (idStx : Syntax) : TermElabM (Option (Sel × Option Nat)) := do
    let some constName ← resolveGlobal? idStx | return none
    match (← getEnv).find? constName with
    | some (.inductInfo _) =>
      if scope.types.contains constName then
        return some (.sig constName (shortName constName), some 1)
      else if scope.lenient then
        return some (.sig constName (shortName constName), some 1)
      else
        throwErrorAt stx m!"type '{constName}' cannot occur in values of \
          '{scope.root}'{suggest scope (shortName constName)}"
    | some (.ctorInfo _) =>
      throwErrorAt stx m!"'{constName}' is a constructor — constructor literals \
        only occur in label comparisons (e.g. `@:x = {shortName constName}`)"
    | _ => return none

/-- A relational expression opposite a value: only a bare ident makes sense, as
    a constructor-label literal. -/
private meta partial def coerceVal (scope : SelScope) (stx : Syntax) :
    TermElabM SelVal := do
  match stx with
  | `(spytial_sel| $x:ident) =>
    if let some v ← resolveCtorLit? scope x then return v
    let some constName ← resolveGlobal? x
      | throwErrorAt x m!"unknown constructor label '{x.getId}'; known labels of \
          '{scope.root}': {", ".intercalate (sortDedup (scope.ctorLabels.toList.map (·.1)).toArray).toList}"
    match (← getEnv).find? constName with
    | some (.ctorInfo ci) =>
      unless ci.numFields == 0 do
        throwErrorAt x m!"'{constName}' has fields — only nullary constructors \
          are atom labels"
      if !scope.types.contains ci.induct && !scope.lenient then
        throwErrorAt x m!"constructor '{constName}' belongs to '{ci.induct}', \
          which cannot occur in values of '{scope.root}'"
      return .ctorLit constName (shortName constName)
    | _ =>
      throwErrorAt x m!"'{constName}' is not a constructor; label comparisons \
        expect a nullary constructor or a literal"
  | s => throwErrorAt s "cannot compare a label value with this operand; a label \
      value compares against a nullary constructor or a string literal — for a \
      numeric label, project with `@num:`"

/-- Elaborate a comparison, choosing the value / integer / relational reading. -/
private meta partial def elabCmp (scope : SelScope) (env : LEnv) (stx : Syntax)
    (op : IntCmp) (rel : Bool) (a b : Syntax) : TermElabM SelForm := do
  -- Syntactic classification of the definite value / integer operands.
  let classify (s : Syntax) : Option Bool :=   -- some true = value, some false = int
    match s.getKind with
    | `selProjPlain | `selProjStr | `selProjBool | ``selStr => some true
    | `selProjNum | ``selCard | ``selNum | ``selNegNum => some false
    | _ => none
  let intCmp : Bool := op matches .lt | .gt | .le | .ge
  let asVal (s : Syntax) : TermElabM SelVal := do
    match classify s with
    | some true => match ← elabExpr scope env s with
      | .val v => return v
      | _ => throwErrorAt s "expected a label/literal value"
    | _ => coerceVal scope s
  let asInt (s : Syntax) : TermElabM SelInt := elabInt scope env s
  let mkV (x y : SelVal) : SelForm := if rel && op == .ne then .vneq x y else .veq x y
  let mkI (x y : SelInt) : SelForm := .icmp op x y
  if intCmp then
    return mkI (← asInt a) (← asInt b)
  -- `@bool:…` opposite a bare `true`/`false` is a boolean-literal comparison
  -- (SGQ evaluates it directly); against `@:`/`@str:` the ident keeps its
  -- constructor-label reading, so this fires only for the `@bool:` projection.
  let boolLitIdent? (s : Syntax) : Option Bool :=
    if s.getKind == ``selIdent then
      match s[0].getId.toString with
      | "true" => some true | "false" => some false | _ => none
    else none
  if a.getKind == `selProjBool then
    if let some bl := boolLitIdent? b then return mkV (← asVal a) (.boolLit bl)
  if b.getKind == `selProjBool then
    if let some bl := boolLitIdent? a then return mkV (.boolLit bl) (← asVal b)
  match classify a, classify b with
  | some true, _ | _, some true => return mkV (← asVal a) (← asVal b)
  | some false, _ | _, some false => return mkI (← asInt a) (← asInt b)
  | none, none =>
    -- Both operands are plain expressions: infer relational vs value vs integer.
    let ea ← elabExpr scope env a
    let eb ← elabExpr scope env b
    match ea, eb with
    | .rel sa aa, .rel sb ab =>
      discard <| sameArity stx (if rel && op == .ne then "!=" else "=") aa ab
      return if rel && op == .ne then .neq sa sb else .eq sa sb
    | .int ia, .int ib => return mkI ia ib
    | .val va, .val vb => return mkV va vb
    | .val va, .rel .. => return mkV va (← coerceVal scope b)
    | .rel .., .val vb => return mkV (← coerceVal scope a) vb
    | _, _ => throwErrorAt stx "cannot compare a relational expression with a \
        label or integer; the two operands have different kinds"

private meta partial def elabForm (scope : SelScope) (env : LEnv) :
    Syntax → TermElabM SelForm
  | stx@`(spytial_sel_form| $a:spytial_sel = $b)   => elabCmp scope env stx .eq true a b
  | stx@`(spytial_sel_form| $a:spytial_sel != $b)  => elabCmp scope env stx .ne true a b
  | stx@`(spytial_sel_form| $a:spytial_sel < $b)   => elabCmp scope env stx .lt false a b
  | stx@`(spytial_sel_form| $a:spytial_sel > $b)   => elabCmp scope env stx .gt false a b
  | stx@`(spytial_sel_form| $a:spytial_sel <= $b)  => elabCmp scope env stx .le false a b
  | stx@`(spytial_sel_form| $a:spytial_sel >= $b)  => elabCmp scope env stx .ge false a b
  | stx@`(spytial_sel_form| $a:spytial_sel =< $b)  => elabCmp scope env stx .le false a b
  | stx@`(spytial_sel_form| $a:spytial_sel in $b) => do
    let (sa, aa) ← elabRel scope env a
    let (sb, ab) ← elabRel scope env b
    discard <| sameArity stx "in" aa ab
    return .subset sa sb
  | stx@`(spytial_sel_form| $a:spytial_sel !in $b) => do
    let (sa, aa) ← elabRel scope env a
    let (sb, ab) ← elabRel scope env b
    discard <| sameArity stx "!in" aa ab
    return .notSubset sa sb
  | `(spytial_sel_form| ! $a)   => return .not (← elabForm scope env a)
  | `(spytial_sel_form| not $a) => return .not (← elabForm scope env a)
  | `(spytial_sel_form| some $a:spytial_sel) => return .some_ (← elabRel scope env a).1
  | `(spytial_sel_form| no $a:spytial_sel)   => return .no (← elabRel scope env a).1
  | `(spytial_sel_form| lone $a:spytial_sel) => return .lone (← elabRel scope env a).1
  | `(spytial_sel_form| one $a:spytial_sel)  => return .one (← elabRel scope env a).1
  | `(spytial_sel_form| ($f)) => elabForm scope env f
  | stx => do
    let k := stx.getKind
    -- Declared quantifier / `let` kinds (namespace-qualified) …
    if k == ``selQAll then elabQuant scope env .all stx
    else if k == ``selQNo then elabQuant scope env .no stx
    else if k == ``selQSome then elabQuant scope env .some stx
    else if k == ``selQLone then elabQuant scope env .lone stx
    else if k == ``selQOne then elabQuant scope env .one stx
    else if k == ``selLet then elabLet scope env stx
    -- … and the hand-written parser kinds (simple names).
    else if k == `selNotIn then do
      let (sa, aa) ← elabRel scope env stx[0]
      let (sb, ab) ← elabRel scope env stx[3]
      discard <| sameArity stx "not in" aa ab
      return .notSubset sa sb
    else if k == `selNi then do
      -- Forge: `a ni b ≡ b in a`. Desugar to the flipped subset (SGQ's own `ni`
      -- computes ¬subset, so we never emit it).
      let (sa, aa) ← elabRel scope env stx[0]
      let (sb, ab) ← elabRel scope env stx[2]
      discard <| sameArity stx "ni" aa ab
      return .subset sb sa
    else if k == `selNotNi then do
      -- `a !ni b` / `a not ni b` ≡ `b !in a`.
      let (sa, aa) ← elabRel scope env stx[0]
      let (sb, ab) ← elabRel scope env stx[3]
      discard <| sameArity stx "!ni" aa ab
      return .notSubset sb sa
    else if k == `selOr then return .or (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    else if k == `selXor then return .xor (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    else if k == `selIff then return .iff (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    else if k == `selAnd then return .and (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    else if k == `selImplies then return .implies (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    else if k == `selIte then
      return .ite (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
        (← elabForm scope env stx[4])
    else throwErrorAt stx "unexpected formula syntax"

/-- A quantified formula `Q disj? x, y : A, … | φ`. The keyword node lays out
    `[kw, optDisj, binders, "|", body]`. -/
private meta partial def elabQuant (scope : SelScope) (env : LEnv) (q : Quant)
    (stx : Syntax) : TermElabM SelForm := do
  let disj := !stx[1].isNone
  let (binders, env') ← elabBinderGroups scope env "quantifier" stx[2].getSepArgs
  let body ← elabForm scope env' stx[4]
  return .quant q disj binders body

/-- `let x = e, … | φ` — desugar by substitution: each binding elaborates in the
    surrounding scope and is stored in `env`, so uses inline it and SGQ never
    sees a `let`. A later comprehension/quantifier binder shadows the `let`. -/
private meta partial def elabLet (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM SelForm := do
  let mut env := env
  for bind in stx[1].getSepArgs do
    let x := bind[0].getId
    let e ← elabExpr scope env bind[2]
    env := (x, .letE e) :: env
  elabForm scope env stx[3]

end

/-! ## Entry points -/

/-- What arity an op position accepts. `pair` positions (orientation, align,
    cyclic) tolerate wider tuples at runtime by projecting first/last, so wider
    is a warning rather than an error there. -/
meta inductive ArityExpect where
  | unary
  | pair
  | unaryOrPair
  deriving Repr, Inhabited

/-- Elaborate a selector against `scope`, enforcing the op position's arity
    expectation (skipped when the arity is statically unknown). A whole-selector
    string literal is the escape hatch (a verbatim, unchecked SGQ expression). -/
meta def elabSelector (scope : SelScope) (expect : ArityExpect)
    (stx : TSyntax `spytial_sel) : TermElabM Sel := do
  if let `(spytial_sel| $s:str) := stx then
    return .raw s.getString
  let (sel, arity) ← elabRel scope [] stx
  if let some a := arity then
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
    | .unaryOrPair =>
      unless a == 1 || a == 2 do
        throwErrorAt stx m!"this position selects atoms or pairs (arity 1 or \
          2), but the selector has arity {a}"
  return sel

/-- Check that an ident names a known relation (an `edgeColor`/`hideField`/
    `attribute` target); returns the relation name string. -/
meta def elabFieldName (scope : SelScope) (stx : TSyntax `ident) : TermElabM String := do
  let s := stx.getId.toString
  if scope.rels.contains s || scope.introduced.contains s then
    return s
  unknownName scope stx s!"relation '{s}'" s

end

end SpytialLean

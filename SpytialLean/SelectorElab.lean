module

public import Lean
public meta import SpytialLean.Selector
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer

namespace SpytialLean

open Lean Elab Meta

public section

/-! # SelectorElab — checked selector syntax

Selectors are Lean syntax (categories `spytial_sel` and `spytial_sel_form`),
elaborated against a `SelScope`: the vocabulary of sigs, relations, and
nullary-constructor labels the relationalizer can emit for the target type.
Every identifier must resolve and every operator's arity must check. A renamed
field or a typo is a compile error at the ident, not an empty selection at
render time.

An expression elaborates to one of three kinds (`EExpr`): relational, value,
or integer. Each position accepts specific kinds. This rejects SGQ's silent
scalar/tuple confusion (`some #e`) at compile time.

A scope is strict when the vocabulary is closed: a monomorphic type built from
monomorphic fields. A type parameter, function-typed field, custom
relationalizer, or non-inductive in the closure makes the scope lenient. The
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

/-- Stop the closure walk where the walker stops decomposing: `Nat` and
    `String` render as literal atoms, `Float` is opaque (not an inductive).
    Other scalar-ish types (`Int`, `Char`, `UInt*`) render as constructor
    chains today, so their closures stay in the vocabulary. -/
private meta def scalarTypes : List Name :=
  [``Nat, ``String, ``Float]

meta def SelScope.ofType (root : Name) : MetaM SelScope := do
  let env ← getEnv
  let mut scope : SelScope := { root }
  -- Stuck-match nodes can appear in any open value, typed at the scrutinized type.
  scope := { scope with rels := scope.rels.insert "scrutinee" root }
  let mut queue : Array Name := #[root]
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
        if c.fields.isEmpty then
          scope := { scope with ctorLabels := scope.ctorLabels.insert c.ctorShort c.ctorName }
        for f in c.fields do
          unless f.isProofLike do
            scope := { scope with rels := scope.rels.insert f.relName t }
            match f.typeHead with
            | some ft => queue := queue.push ft
            | none => scope := { scope with lenient := true }
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

/-- For error messages only. -/
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
    selects nothing at render (engine limitation)"

/-! ## Syntax

The grammar replicates Forge's expression/formula cascade over two categories.
Both use `behavior := both`, so keyword-led rules compile to
`nonReservedSymbol` and a relation named `some` still parses. Forms with a
mandatory further token win by longest-match; the nullary constants tie with a
bare ident, so they take `priority := high`. The precedence numbers are
Forge's cascade re-scaled, loosest at the top. -/

open Lean Parser

-- `nonReservedSymbol` registers no token, so an `@:`-family head would
-- maximal-munch onto the global `@`; those rules are hand-written below with
-- reserved `symbol` heads.
declare_syntax_cat spytial_sel (behavior := both)
declare_syntax_cat spytial_sel_form (behavior := both)

syntax spytialSelBinderGroup := sepBy1(ident, ", ") " : " spytial_sel

/-! ### Relational / integer expressions (`spytial_sel`), loosest → tightest -/

syntax:30 spytial_sel:30 " + " spytial_sel:31 : spytial_sel
syntax:30 spytial_sel:30 " - " spytial_sel:31 : spytial_sel
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
syntax:100 (name := selStr) str : spytial_sel
syntax:100 (name := selNum) num : spytial_sel
syntax:100 (name := selNegNum) "-" noWs num : spytial_sel
/-- Backquote atom literal (`` `a0 ``), spelled with Lean's `name` literal. -/
syntax:100 (name := selAtomLit) name : spytial_sel

syntax:100 (name := selUniv) (priority := high) "univ" : spytial_sel
syntax:100 (name := selIden) (priority := high) "iden" : spytial_sel
syntax:100 (name := selNone) (priority := high) "none" : spytial_sel

-- Bare `sum` fails the rule and falls to `selIdent`, so a field named `sum`
-- still parses.
syntax:5 (name := selSum) "sum " ident " : " spytial_sel " | " spytial_sel : spytial_sel

private meta def arrowMultP : Parser :=
  nonReservedSymbol "lone" (includeIdent := true) <|>
    nonReservedSymbol "one" (includeIdent := true) <|>
    nonReservedSymbol "some" (includeIdent := true) <|>
    nonReservedSymbol "set" (includeIdent := true)

/-- Arrow-multiplicity product (`A one -> lone B`). `includeIdent` lets a left
    annotation trigger the trailing parser; the right side is `atomic`, so a
    relation named `one`/`lone` still works as the bare operand. -/
@[spytial_sel_parser] meta def selProdOp : TrailingParser :=
  trailingNode `selProd 50 50
    (Lean.Parser.optional arrowMultP >> symbol "->" >>
      ((Lean.Parser.atomic (arrowMultP >> categoryParser `spytial_sel 51)) <|>
        (Lean.Parser.pushNone >> categoryParser `spytial_sel 51)))

/-! ### Formulas (`spytial_sel_form`), loosest → tightest -/

syntax:5 (name := selQAll)  "all "  (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form
syntax:5 (name := selQNo)   "no "   (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form
syntax:5 (name := selQSome) "some " (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form
syntax:5 (name := selQLone) "lone " (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form
syntax:5 (name := selQOne)  "one "  (&" disj")? spytialSelBinderGroup,+ " | " spytial_sel_form:5 : spytial_sel_form

syntax:5 (name := selLet) "let " sepBy1(ident " = " spytial_sel, ", ") " | " spytial_sel_form:5 : spytial_sel_form

-- `=<` is Forge's alias for `<=`
syntax:50 spytial_sel " = "   spytial_sel : spytial_sel_form
syntax:50 spytial_sel " != "  spytial_sel : spytial_sel_form
syntax:50 spytial_sel " in "  spytial_sel : spytial_sel_form
-- `!in` must stay the two existing tokens `!` `in`: a `"!in"` atom would
-- enter the global token table and steal the prefix of negations like
-- `!input` in every importing module.
syntax:50 spytial_sel " !" "in " spytial_sel : spytial_sel_form
syntax:50 spytial_sel " < "   spytial_sel : spytial_sel_form
syntax:50 spytial_sel " > "   spytial_sel : spytial_sel_form
syntax:50 spytial_sel " <= "  spytial_sel : spytial_sel_form
syntax:50 spytial_sel " >= "  spytial_sel : spytial_sel_form
syntax:50 spytial_sel " =< "  spytial_sel : spytial_sel_form

-- `a not in b`, `a ni b`, `a !ni b`, `a not ni b`. These are hand-written:
-- `syntax` rules would reserve `not`/`ni` for every importing module.
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

syntax:60 "some " spytial_sel:30 : spytial_sel_form
syntax:60 "no "   spytial_sel:30 : spytial_sel_form
syntax:60 "lone " spytial_sel:30 : spytial_sel_form
syntax:60 "one "  spytial_sel:30 : spytial_sel_form

syntax:40 "! "  spytial_sel_form:40 : spytial_sel_form
syntax:40 "not " spytial_sel_form:40 : spytial_sel_form

syntax:100 "(" spytial_sel_form ")" : spytial_sel_form

private meta def connOp (kind : SyntaxNodeKind) (prec lhsPrec rhsPrec : Nat) (opP : Parser) :
    TrailingParser :=
  trailingNode kind prec lhsPrec (opP >> categoryParser `spytial_sel_form rhsPrec)

-- `includeIdent` indexes the word spelling under `identKind`, so the
-- behavior-blind trailing loop reaches it after any formula.
private meta def wordSym (sym word : String) : Parser :=
  symbol sym <|> nonReservedSymbol word (includeIdent := true)

@[spytial_sel_form_parser] meta def selOrOp   : TrailingParser := connOp `selOr   10 10 11 (wordSym "||" "or")
@[spytial_sel_form_parser] meta def selXorOp  : TrailingParser := connOp `selXor  13 13 14 (nonReservedSymbol "xor" (includeIdent := true))
@[spytial_sel_form_parser] meta def selIffOp  : TrailingParser := connOp `selIff  16 16 17 (wordSym "<=>" "iff")
@[spytial_sel_form_parser] meta def selImpOp  : TrailingParser := connOp `selImplies 20 21 20 (wordSym "=>" "implies")
@[spytial_sel_form_parser] meta def selAndOp  : TrailingParser := connOp `selAnd  30 30 31 (wordSym "&&" "and")

@[spytial_sel_form_parser] meta def selIteOp : TrailingParser :=
  trailingNode `selIte 20 21
    (wordSym "=>" "implies" >> categoryParser `spytial_sel_form 21 >>
      symbol "else" >> categoryParser `spytial_sel_form 20)

/-! ## Elaboration

Relational results carry an arity. `none` means statically unknown (`raw`, or
a lenient pass-through) and disables downstream arity checks. -/

/-- The typed result of elaborating a `spytial_sel`. Compile-time only; never
    stored. -/
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

/-- Adds hover/go-to-def info on success. -/
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

/-- The nullary-constructor label a bare ident denotes, with hover info. -/
private meta def resolveCtorLit? (scope : SelScope) (stx : Syntax) : TermElabM (Option SelVal) := do
  if let some ctorName := scope.ctorLabels.get? stx.getId.toString then
    if let some e ← try pure (some (← mkConstWithLevelParams ctorName)) catch _ => pure none then
      discard <| Term.addTermInfo stx e
    return some (.ctorLit ctorName (shortName ctorName))
  return none

mutual

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
    let (sa, aa) ← elabRel scope env a
    let (sb, ab) ← elabRel scope env b
    return .rel (.override sa sb) (← sameArity stx "++" aa ab)
  | `(spytial_sel| $a <: $b) => do
    let (sa, _) ← elabRel scope env a
    let (sb, ab) ← elabRel scope env b
    return .rel (.restrictDom sa sb) ab
  | `(spytial_sel| $a :> $b) => do
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
    match a.raw.isNameLit? with
    | some n => return .rel (.atomLit n.toString) (some 1)
    | none => throwErrorAt stx "malformed atom literal"
  | `(spytial_sel| {$groups,* | $body}) => do
    let (binders, env') ← elabBinderGroups scope env "comprehension" (groups.getElems.map (·.raw))
    let bodyForm ← elabForm scope env' body
    return .rel (.compr binders bodyForm) (some binders.size)
  | stx =>
    match stx.getKind with
    | `selProjPlain => return .val (← elabLabel scope env .plain ⟨stx[1]⟩)
    | `selProjStr   => return .val (← elabLabel scope env .str ⟨stx[1]⟩)
    | `selProjBool  => return .val (← elabLabel scope env .bool ⟨stx[1]⟩)
    | `selProjNum   => do
      let (sel, arity) ← elabRel scope env stx[1]
      checkArity stx[1] "a label projection's operand" arity 1
      return .int (.proj sel)
    | `selProd => elabProd scope env stx
    | _ => elabBoxJoin? scope env stx

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
        checkArity argSyns[0]! s!"the argument of {hn}[e]" aa 1
        return .int (.agg op sa)
      elabRelBoxJoin scope env stx head argSyns
    | none => elabRelBoxJoin scope env stx head argSyns
  | _ => throwErrorAt stx "unexpected selector syntax"

/-- `e[a, b] ≡ b.a.e` (Forge). -/
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

/-- Node shape: `[lhs, leftOpt, "->", rightMultOrNull, rhs]` (see `selProdOp`). -/
private meta partial def elabProd (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM EExpr := do
  let lm := if stx[1].getNumArgs == 0 then none else arrowMultOf? stx[1][0]
  let rm := arrowMultOf? stx[3]
  let (sa, aa) ← elabRel scope env stx[0]
  let (sb, ab) ← elabRel scope env stx[4]
  let arity : Option Nat := do return (← aa) + (← ab)
  if lm.isSome || rm.isSome then
    return .rel (.prodMult sa lm rm sb) arity
  return .rel (.prod sa sb) arity
where
  arrowMultOf? (s : Syntax) : Option ArrowMult :=
    match s.getAtomVal with
    | "lone" => some .lone | "one" => some .one
    | "some" => some .some | "set" => some .set | _ => none

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

private meta partial def elabRel (scope : SelScope) (env : LEnv) (stx : Syntax) :
    TermElabM (Sel × Option Nat) := do
  match ← elabExpr scope env stx with
  | .rel s a => return (s, a)
  | .int _ => throwErrorAt stx "this position expects a relational expression, \
      but the selector is an integer (`#`, a numeral, `@num:`, or an int builtin)"
  | .val _ => throwErrorAt stx "this position expects a relational expression, \
      but the selector is a label/literal value"

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

/-- Resolution order: local binding, nullary-constructor label, vocabulary.
    Dotted components fold as joins unless a prefix names a type. -/
private meta partial def resolveExprIdent (scope : SelScope) (env : LEnv)
    (stx : TSyntax `ident) : TermElabM EExpr := do
  match stx.getId.components with
  | [] => throwErrorAt stx "empty selector name"
  | head :: rest =>
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
      if let some v ← resolveCtorLit? scope stx then
        return .val v
    let (sel, arity, unconsumed) ← resolveHead stx head rest
    joinRest sel arity unconsumed
where
  joinRest (sel : Sel) (arity : Option Nat) (rest : List Name) : TermElabM EExpr := do
    let s ← rest.foldlM (init := (sel, arity)) fun (sel, arity) comp => do
      let compStr := comp.toString
      let compArity? : Option Nat :=
        if scope.rels.contains compStr then some 2
        else scope.introduced.get? compStr
      match compArity? with
      | some ca =>
        unless scope.rels.contains compStr do warnGraphSideName stx compStr
        return (.join sel (.rel compStr), ← joinArity stx arity (some ca))
      | none => unknownName scope stx s!"relation '{compStr}'" (Sel.join sel (.rel compStr), none)
    return .rel s.1 s.2
  resolveHead (idStx : Syntax) (head : Name) (rest : List Name) :
      TermElabM (Sel × Option Nat × List Name) := do
    let s := head.toString
    if scope.rels.contains s then return (.rel s, some 2, rest)
    if let some arity := scope.introduced.get? s then
      warnGraphSideName idStx s
      return (.rel s, some arity, rest)
    -- Longest prefix that names a type wins (`SelQual.Inner.someField`): try
    -- the full name, then shorter prefixes; the unconsumed tail folds as joins.
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

private meta partial def elabCmp (scope : SelScope) (env : LEnv) (stx : Syntax)
    (op : IntCmp) (rel : Bool) (a b : Syntax) : TermElabM SelForm := do
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
  -- against `@:`/`@str:` a bare `true`/`false` keeps the constructor-label reading
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
  | stx =>
    match stx.getKind with
    -- Declared quantifier / `let` kinds (namespace-qualified) …
    | ``selQAll  => elabQuant scope env .all stx
    | ``selQNo   => elabQuant scope env .no stx
    | ``selQSome => elabQuant scope env .some stx
    | ``selQLone => elabQuant scope env .lone stx
    | ``selQOne  => elabQuant scope env .one stx
    | ``selLet   => elabLet scope env stx
    -- … and the hand-written parser kinds (simple names).
    | `selNotIn => do
      let (sa, aa) ← elabRel scope env stx[0]
      let (sb, ab) ← elabRel scope env stx[3]
      discard <| sameArity stx "not in" aa ab
      return .notSubset sa sb
    | `selNi => do
      let (sa, aa) ← elabRel scope env stx[0]
      let (sb, ab) ← elabRel scope env stx[2]
      discard <| sameArity stx "ni" aa ab
      return .ni sa sb
    | `selNotNi => do
      let (sa, aa) ← elabRel scope env stx[0]
      let (sb, ab) ← elabRel scope env stx[3]
      discard <| sameArity stx "!ni" aa ab
      return .notNi sa sb
    | `selOr      => return .or (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    | `selXor     => return .xor (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    | `selIff     => return .iff (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    | `selAnd     => return .and (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    | `selImplies => return .implies (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
    | `selIte =>
      return .ite (← elabForm scope env stx[0]) (← elabForm scope env stx[2])
        (← elabForm scope env stx[4])
    | _ => throwErrorAt stx "unexpected formula syntax"

/-- Node layout: `[kw, optDisj, binders, "|", body]`. -/
private meta partial def elabQuant (scope : SelScope) (env : LEnv) (q : Quant)
    (stx : Syntax) : TermElabM SelForm := do
  let disj := !stx[1].isNone
  let (binders, env') ← elabBinderGroups scope env "quantifier" stx[2].getSepArgs
  let body ← elabForm scope env' stx[4]
  return .quant q disj binders body

/-- Desugars by substitution — SGQ has no `let`. A later binder shadows the
    `let`. -/
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

/-- `pair` positions project first/last at runtime, so a wider selector warns
    rather than errors. -/
meta inductive ArityExpect where
  | unary
  | pair
  | unaryOrPair
  deriving Repr, Inhabited

/-- A whole-selector string literal is the raw escape hatch. -/
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

meta def elabFieldName (scope : SelScope) (stx : TSyntax `ident) : TermElabM String := do
  let s := stx.getId.toString
  if scope.rels.contains s || scope.introduced.contains s then
    return s
  unknownName scope stx s!"relation '{s}'" s

end

end SpytialLean

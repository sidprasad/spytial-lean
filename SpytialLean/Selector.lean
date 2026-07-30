module

public import Lean

namespace SpytialLean

open Lean

/-! # Selector — the reified SGQ expression language

The selector language spytial-core evaluates is the Forge expression language
(via the `simple-graph-query` ANTLR evaluator) extended with label-projection
operators (`@:`, `@str:`, `@bool:`, `@num:`). This module reifies the fragment
Spytial specs use as plain data: relational expressions (`Sel`), a typed integer
sub-language (`SelInt`), label/literal values (`SelVal`), and formulas
(`SelForm`, the bodies of set comprehensions and quantifiers).

The AST is what a `spytial_spec` stores in the environment (it must pickle into
`.olean`s), so nodes carry no `Syntax` — name resolution and checking happen in
the elaborator (`SpytialLean.SelectorElab`), which records resolved Lean names
here alongside the strings the relationalizer actually emits. Lowering back to
the concrete SGQ string consumed by spytial-core is `Sel.toSGQ`.

The surface grammar mirrors Forge; a few forms Forge parses are currently
*mislowered by the SGQ engine* (`<:`, `:>`, `++`, `->`-multiplicity
annotations). We reify and emit them faithfully (Forge semantics) so a corpus
author can write them, and the elaborator attaches a warning naming the upstream
engine bug and its interim workaround — see the `FIXME(sgq …)` markers below.
-/

/-- Which label projection a `SelVal.label` performs: `@:` reads an atom's label
    as a string; the typed variants coerce (`@str:`, `@bool:`). Numeric reads
    (`@num:`) are int-typed and live in `SelInt.proj`. -/
public meta inductive LabelProj where
  | plain | str | bool
  deriving Repr, BEq, Inhabited

/-- Arrow multiplicity annotation on a product (`A one -> lone B`). Forge parses
    these; the SGQ engine silently drops them (`FIXME(sgq arrow-mult)`). -/
public meta inductive ArrowMult where
  | lone | one | some | set
  deriving Repr, BEq, Inhabited

/-- An integer builtin applied through box-join syntax (`add[a, b]`, `abs[x]`). -/
public meta inductive IntBuiltin where
  | add | subtract | multiply | divide | remainder | abs | sign
  deriving Repr, BEq, Inhabited

/-- An integer aggregator over a relational expression (`sum[e]`, `min[e]`). -/
public meta inductive IntAgg where
  | sum | min | max
  deriving Repr, BEq, Inhabited

/-- An integer comparison operator (int-typed operands only, except `=`/`!=`
    which are shared with the relational/value layers by the checker). -/
public meta inductive IntCmp where
  | eq | ne | lt | gt | le | ge
  deriving Repr, BEq, Inhabited

/-- A leading multiplicity/quantifier keyword. As a quantifier it binds
    variables (`some x : A | φ`); as a multiplicity it constrains one expression
    (`some e`). -/
public meta inductive Quant where
  | all | no | some | lone | one
  deriving Repr, BEq, Inhabited

mutual

/-- A relational expression over the data instance: atoms are type sigs
    (arity 1) and field relations (arity 2), composed by the Alloy operator
    algebra. `sig` keeps the resolved Lean name (so a stored spec still says
    *which* type it meant) next to the sig string the relationalizer emits. -/
public meta inductive Sel where
  | sig (typeName : Name) (sig : String)
  | rel (name : String)
  | var (x : Name)
  | univ
  | iden
  | none_
  /-- A backquote atom literal (`` `a0 ``) — a specific atom by name. -/
  | atomLit (name : String)
  | union (a b : Sel)
  | diff (a b : Sel)
  | inter (a b : Sel)
  | prod (a b : Sel)
  /-- Product with arrow-multiplicity annotations (`A one -> lone B`).
      `FIXME(sgq arrow-mult)`: SGQ parses then silently drops the annotations. -/
  | prodMult (a : Sel) (lm rm : Option ArrowMult) (b : Sel)
  | join (a b : Sel)
  /-- `FIXME(sgq override)`: SGQ throws on `++` at evaluation. -/
  | override (a b : Sel)
  /-- Domain restriction `a <: b`. `FIXME(sgq restrict)`: SGQ throws. -/
  | restrictDom (a b : Sel)
  /-- Range restriction `a :> b`. `FIXME(sgq restrict)`: SGQ throws. -/
  | restrictRan (a b : Sel)
  | trans (a : Sel)
  | reflTrans (a : Sel)
  | transpose (a : Sel)
  | compr (binders : Array (Name × Sel)) (body : SelForm)
  /-- Escape hatch: an unchecked SGQ string, lowered verbatim. For selectors
      whose vocabulary the checker cannot know (custom relationalizers,
      genuinely dynamic queries). The body is arbitrary SGQ, so when composed
      it binds loosest and is parenthesized in any tighter context. -/
  | raw (sgq : String)
  deriving Repr, BEq

/-- A typed integer expression. Int-typed positions (int comparisons, box-join
    builtin arguments, `sum`-quantifier bodies) accept exactly these; tuple
    positions reject them. This kills SGQ's silent scalar/tuple confusion (e.g.
    `some #e` evaluates to false with no error) at authoring time. -/
public meta inductive SelInt where
  | lit (n : Int)
  | card (e : Sel)                                   -- `#e`
  | proj (e : Sel)                                   -- `@num:e`
  | builtin (op : IntBuiltin) (args : Array SelInt)  -- `add[a, b]`
  | agg (op : IntAgg) (e : Sel)                      -- `sum[e]`, `min[e]`, `max[e]`
  /-- `sum x : A | ie` — Forge's integer aggregation quantifier (sum of the
      integer body `ie` over all `x` in `A`). Single binder, per Forge's
      expander. Unlike the `sum[e]` aggregator, SGQ evaluates this correctly, so
      it carries no warning. -/
  | sumQuant (x : Name) (dom : Sel) (body : SelInt)
  deriving Repr, BEq

/-- A label/literal value, the operands of `@:`-style comparisons. A nullary
    constructor used as a literal (`@:x = tt`) resolves to the constructor and
    lowers to the label the relationalizer gives its atoms (the short name). -/
public meta inductive SelVal where
  | label (proj : LabelProj) (e : Sel)
  | ctorLit (ctor : Name) (label : String)
  | strLit (s : String)
  | boolLit (b : Bool)
  deriving Repr, BEq

/-- A formula — the body of a set comprehension or quantifier. -/
public meta inductive SelForm where
  | subset (a b : Sel)
  /-- `a !in b` / `a not in b`. -/
  | notSubset (a b : Sel)
  | eq (a b : Sel)
  | neq (a b : Sel)
  | veq (a b : SelVal)
  | vneq (a b : SelVal)
  | icmp (op : IntCmp) (a b : SelInt)
  | and (a b : SelForm)
  | or (a b : SelForm)
  | xor (a b : SelForm)
  | iff (a b : SelForm)
  | implies (a b : SelForm)
  /-- Formula-level if-then-else (`a => b else c`). -/
  | ite (c t e : SelForm)
  | not (a : SelForm)
  | some_ (a : Sel)
  | no (a : Sel)
  | lone (a : Sel)
  | one (a : Sel)
  /-- Quantified formula (`Q disj? x, y : A, z : B | φ`). -/
  | quant (q : Quant) (disj : Bool) (binders : Array (Name × Sel)) (body : SelForm)
  deriving Repr, BEq

end

public meta instance : Inhabited Sel := ⟨.univ⟩
public meta instance : Inhabited SelInt := ⟨.lit 0⟩
public meta instance : Inhabited SelVal := ⟨.strLit ""⟩
public meta instance : Inhabited SelForm := ⟨.some_ .univ⟩

namespace Sel

/-- Binding strength of a relational expression, mirroring Forge's tight-end
    cascade (Expr8–Expr18): union/difference loosest, then override, intersection,
    product, restrictions, join; unary closure operators and atoms tightest. -/
public meta def prec : Sel → Nat
  | raw .. => 0
  | union .. | diff .. => 30
  | override .. => 36
  | inter .. => 40
  | prod .. | prodMult .. => 50
  | restrictDom .. | restrictRan .. => 55
  | join .. => 60
  | trans .. | reflTrans .. | transpose .. => 70
  | _ => 100

end Sel

private meta def parenIf (needed : Bool) (s : String) : String :=
  if needed then s!"({s})" else s

/-- Identifiers the SGQ (Forge) lexer reserves as tokens: a vocabulary name that
    collides must be backtick-quoted or the engine fails to parse the selector.
    Mirrors `RESERVED_KEYWORDS` in simple-graph-query, whose own expression
    synthesis quotes the same way. -/
private meta def sgqReserved : List String :=
  ["open", "as", "var", "abstract", "sig", "extends", "in",
   "lone", "some", "one", "two", "set", "func", "pfunc", "disj",
   "wheat", "pred", "fun", "assert", "run", "check", "for", "but",
   "exactly", "none", "univ", "iden", "is", "sat", "unsat", "theorem",
   "forge_error", "checked", "test", "expect", "suite", "all",
   "sufficient", "necessary", "consistent", "inconsistent", "with",
   "let", "bind", "or", "xor", "iff", "implies", "else", "and",
   "until", "release", "since", "triggered", "not", "always",
   "eventually", "after", "before", "once", "historically", "this",
   "sexpr", "inst", "eval", "example", "ni", "no", "sum", "Int", "option"]

/-- Backtick-quote a vocabulary name the SGQ lexer would otherwise read as a
    keyword (`some` → `` `some` ``). -/
private meta def quoteIfReserved (s : String) : String :=
  if sgqReserved.contains s then s!"`{s}`" else s
/-- How SGQ spells `c` inside a double-quoted literal. Its unquoting resolves
    exactly `\n`, `\t`, `\r`, `\0`, `\"` and `\\` and drops the backslash from
    every other escape, so those six are the whole escape alphabet and any other
    character has to ride raw. `none` marks a character with no spelling either
    way: a C0 control or DEL without an escape of its own, which would have to
    ride raw through the spec's JSON/YAML hop and does not survive it. -/
private meta def sgqStringChar? : Char → Option String
  | '\\' => some "\\\\"
  | '"' => some "\\\""
  | '\n' => some "\\n"
  | '\t' => some "\\t"
  | '\r' => some "\\r"
  | '\x00' => some "\\0"
  | c => if c.val < 0x20 || c.val == 0x7f then none else some c.toString

/-- The first character of `s` that SGQ's string syntax cannot spell, for the
    elaborator to reject before it reaches a lowering. Only a user-written
    string literal can trip this — identifier-derived labels carry no controls. -/
public meta def sgqUnspellableChar? (s : String) : Option Char :=
  s.toList.find? fun c => (sgqStringChar? c).isNone

/-- Render `s` as an SGQ double-quoted string literal. An unspellable character
    is emitted raw, the closest thing to right for a case the elaborator has
    already rejected. -/
public meta def sgqStringLit (s : String) : String :=
  let body := s.toList.map fun c => (sgqStringChar? c).getD c.toString
  s!"\"{String.join body}\""

private meta def ArrowMult.toSGQ : ArrowMult → String
  | .lone => "lone" | .one => "one" | .some => "some" | .set => "set"

private meta def IntBuiltin.toSGQ : IntBuiltin → String
  | .add => "add" | .subtract => "subtract" | .multiply => "multiply"
  | .divide => "divide" | .remainder => "remainder" | .abs => "abs" | .sign => "sign"

private meta def IntAgg.toSGQ : IntAgg → String
  | .sum => "sum" | .min => "min" | .max => "max"

private meta def IntCmp.toSGQ : IntCmp → String
  | .eq => "=" | .ne => "!=" | .lt => "<" | .gt => ">" | .le => "<=" | .ge => ">="

private meta def Quant.toSGQ : Quant → String
  | .all => "all" | .no => "no" | .some => "some" | .lone => "lone" | .one => "one"

/-- Print grouped comprehension/quantifier binders: adjacent binders of one
    domain share a type (`x, y : BDD, z : Nat`). -/
private meta def bindersToSGQ (binders : Array (Name × Sel)) (domToSGQ : Sel → String) :
    String :=
  let groups := binders.foldl (init := #[]) fun (gs : Array (Array Name × Sel)) (x, dom) =>
    match gs.back? with
    | some (xs, dom') =>
      if dom' == dom then gs.set! (gs.size - 1) (xs.push x, dom') else gs.push (#[x], dom)
    | none => gs.push (#[x], dom)
  ", ".intercalate <| groups.toList.map fun (xs, dom) =>
    let names := ", ".intercalate (xs.toList.map (quoteIfReserved <| toString ·))
    s!"{names} : {domToSGQ dom}"

mutual

/-- Lower to the concrete SGQ string, parenthesizing only where precedence
    demands. `ctx` is the binding strength of the enclosing position. -/
public meta partial def Sel.toSGQCtx (ctx : Nat) : Sel → String
  | .sig _ s => quoteIfReserved s
  | .rel r => quoteIfReserved r
  | .var x => quoteIfReserved (toString x)
  | .univ => "univ"
  | .iden => "iden"
  | .none_ => "none"
  | .atomLit a => s!"`{a}"
  | e@(.union a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 30} + {b.toSGQCtx 31}"
  | e@(.diff a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 30} - {b.toSGQCtx 31}"
  | e@(.override a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 36} ++ {b.toSGQCtx 37}"
  | e@(.inter a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 40} & {b.toSGQCtx 41}"
  | e@(.prod a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 50}->{b.toSGQCtx 51}"
  | e@(.prodMult a lm rm b) =>
    let mul (m : Option ArrowMult) := match m with | some m => s!"{m.toSGQ} " | none => ""
    parenIf (e.prec < ctx) s!"{a.toSGQCtx 50} {mul lm}-> {mul rm}{b.toSGQCtx 51}"
  | e@(.restrictDom a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 55} <: {b.toSGQCtx 56}"
  | e@(.restrictRan a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 55} :> {b.toSGQCtx 56}"
  | e@(.join a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 60}.{b.toSGQCtx 61}"
  | .trans a => s!"^{a.toSGQCtx 71}"
  | .reflTrans a => s!"*{a.toSGQCtx 71}"
  | .transpose a => s!"~{a.toSGQCtx 71}"
  | .compr binders body =>
    s!"\{{bindersToSGQ binders (·.toSGQCtx 0)} | {body.toSGQ}}"
  | e@(.raw s) => parenIf (e.prec < ctx) s

/-- Lower an integer expression. Int operators are bracketed/prefix and mostly
    self-delimiting; only `#`'s operand needs precedence-aware parens. -/
public meta partial def SelInt.toSGQ : SelInt → String
  | .lit n => toString n
  -- `#` binds tighter than union/difference but looser than the rest, so only a
  -- union/difference operand needs parens (`#(a + b)`; `#a.b` stays bare).
  | .card e => s!"#{e.toSGQCtx 34}"
  | .proj e => s!"@num:{e.toSGQCtx 100}"
  | .builtin op args => s!"{op.toSGQ}[{", ".intercalate (args.toList.map SelInt.toSGQ)}]"
  | .agg op e => s!"{op.toSGQ}[{e.toSGQCtx 0}]"
  -- The body extends maximally right in SGQ, so a `sum` used as a comparison
  -- operand must be parenthesized (`(sum …) > 2`); always wrap.
  | .sumQuant x dom body =>
    s!"(sum {quoteIfReserved (toString x)} : {dom.toSGQCtx 0} | {body.toSGQ})"

/-- Lower a label/value operand. The projected expression prints at atom
    strength, so `@:x` stays bare while `@:(x.v)` gets its parentheses. -/
public meta partial def SelVal.toSGQ : SelVal → String
  | .label proj e =>
    let tok := match proj with | .plain => "@:" | .str => "@str:" | .bool => "@bool:"
    s!"{tok}{e.toSGQCtx 100}"
  | .ctorLit _ label => sgqStringLit label
  -- The relationalizer labels a `String` atom with its Lean spelling, quotes
  -- included (`Relationalizer.lean`), so matching one takes a literal whose
  -- content carries those quotes too.
  | .strLit s => sgqStringLit s!"\"{s}\""
  | .boolLit b => toString b

/-- Lower a formula. Connective precedence follows Forge's loose-end cascade
    (`or` < `xor` < `iff` < `implies` < `and` < `not`); `implies` is
    right-associative. Comparisons and multiplicities are atomic here. -/
public meta partial def SelForm.toSGQCtx (ctx : Nat) : SelForm → String
  | .subset a b => s!"{a.toSGQCtx 0} in {b.toSGQCtx 0}"
  | .notSubset a b => s!"{a.toSGQCtx 0} !in {b.toSGQCtx 0}"
  | .eq a b => s!"{a.toSGQCtx 0} = {b.toSGQCtx 0}"
  | .neq a b => s!"{a.toSGQCtx 0} != {b.toSGQCtx 0}"
  | .veq a b => s!"{a.toSGQ} = {b.toSGQ}"
  | .vneq a b => s!"{a.toSGQ} != {b.toSGQ}"
  | .icmp op a b => s!"{a.toSGQ} {op.toSGQ} {b.toSGQ}"
  | .or a b => parenIf (10 < ctx) s!"{a.toSGQCtx 10} or {b.toSGQCtx 11}"
  | .xor a b => parenIf (13 < ctx) s!"{a.toSGQCtx 13} xor {b.toSGQCtx 14}"
  | .iff a b => parenIf (16 < ctx) s!"{a.toSGQCtx 16} iff {b.toSGQCtx 17}"
  | .implies a b => parenIf (20 < ctx) s!"{a.toSGQCtx 21} implies {b.toSGQCtx 20}"
  | .ite c t e =>
    parenIf (20 < ctx) s!"{c.toSGQCtx 21} implies {t.toSGQCtx 21} else {e.toSGQCtx 20}"
  | .and a b => parenIf (30 < ctx) s!"{a.toSGQCtx 30} and {b.toSGQCtx 31}"
  | .not a => s!"not {a.toSGQCtx 40}"
  | .some_ a => s!"some {a.toSGQCtx 0}"
  | .no a => s!"no {a.toSGQCtx 0}"
  | .lone a => s!"lone {a.toSGQCtx 0}"
  | .one a => s!"one {a.toSGQCtx 0}"
  -- A quantifier body extends maximally right, so any connective context needs
  -- the parens the surface required (`(all y : A | φ) and ψ`).
  | .quant q disj binders body =>
    let d := if disj then "disj " else ""
    parenIf (5 < ctx) s!"{q.toSGQ} {d}{bindersToSGQ binders (·.toSGQCtx 0)} | {body.toSGQ}"

public meta partial def SelForm.toSGQ (f : SelForm) : String := f.toSGQCtx 0

end

mutual

/-- The `.var` names free in an expression, comprehension/quantifier binders
    subtracted (a later binder's domain may reference an earlier binder, so
    subtraction is positional). Lowering is name-based, so the elaborator uses
    this to reject a `let` substitution an inner binder would capture. -/
public meta partial def Sel.freeVars : Sel → Array Name
  | .var x => #[x]
  | .union a b | .diff a b | .inter a b | .prod a b | .join a b
  | .override a b | .restrictDom a b | .restrictRan a b => a.freeVars ++ b.freeVars
  | .prodMult a _ _ b => a.freeVars ++ b.freeVars
  | .trans a | .reflTrans a | .transpose a => a.freeVars
  | .compr binders body => bindersFreeVars binders body.freeVars
  | .sig .. | .rel .. | .univ | .iden | .none_ | .atomLit .. | .raw .. => #[]

public meta partial def SelVal.freeVars : SelVal → Array Name
  | .label _ e => e.freeVars
  | .ctorLit .. | .strLit .. | .boolLit .. => #[]

public meta partial def SelInt.freeVars : SelInt → Array Name
  | .lit .. => #[]
  | .card e | .proj e | .agg _ e => e.freeVars
  | .builtin _ args => args.foldl (· ++ ·.freeVars) #[]
  | .sumQuant x dom body => dom.freeVars ++ body.freeVars.filter (· != x)

public meta partial def SelForm.freeVars : SelForm → Array Name
  | .subset a b | .notSubset a b | .eq a b | .neq a b =>
    a.freeVars ++ b.freeVars
  | .veq a b | .vneq a b => a.freeVars ++ b.freeVars
  | .icmp _ a b => a.freeVars ++ b.freeVars
  | .and a b | .or a b | .xor a b | .iff a b | .implies a b =>
    a.freeVars ++ b.freeVars
  | .ite c t e => c.freeVars ++ t.freeVars ++ e.freeVars
  | .not a => a.freeVars
  | .some_ a | .no a | .lone a | .one a => a.freeVars
  | .quant _ _ binders body => bindersFreeVars binders body.freeVars

private meta partial def bindersFreeVars (binders : Array (Name × Sel))
    (bodyFrees : Array Name) : Array Name := Id.run do
  let mut bound : Array Name := #[]
  let mut out : Array Name := #[]
  for (x, dom) in binders do
    out := out ++ dom.freeVars.filter (!bound.contains ·)
    bound := bound.push x
  return out ++ bodyFrees.filter (!bound.contains ·)

end

/-- Lower a selector to the concrete SGQ string spytial-core evaluates. -/
public meta def Sel.toSGQ (s : Sel) : String := s.toSGQCtx 0

end SpytialLean

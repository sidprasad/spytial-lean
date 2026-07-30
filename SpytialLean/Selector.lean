module

public import Lean

namespace SpytialLean

open Lean

/-! # Selector — the reified SGQ expression language

This module reifies the Forge expression fragment Spytial specs use, plus the
SGQ label projections (`@:`, `@str:`, `@bool:`, `@num:`): relational
expressions (`Sel`), integer expressions (`SelInt`), label/literal values
(`SelVal`), and formulas (`SelForm`). Specs store this AST in the environment,
so nodes carry no `Syntax` and must pickle into `.olean`s. The elaborator
(`SpytialLean.SelectorElab`) resolves and checks names. `Sel.toSGQ` lowers to
the concrete string spytial-core evaluates.
-/

/-- `@num:` is int-typed and lives in `SelInt.proj`. -/
public meta inductive LabelProj where
  | plain | str | bool
  deriving Repr, BEq, Inhabited

/-- Parsed for Forge grammar parity; the engine rejects multiplicity
    annotations in expression position at render. -/
public meta inductive ArrowMult where
  | lone | one | some | set
  deriving Repr, BEq, Inhabited

public meta inductive IntBuiltin where
  | add | subtract | multiply | divide | remainder | abs | sign
  deriving Repr, BEq, Inhabited

public meta inductive IntAgg where
  | sum | min | max
  deriving Repr, BEq, Inhabited

/-- The checker shares `=`/`!=` with the relational and value layers. -/
public meta inductive IntCmp where
  | eq | ne | lt | gt | le | ge
  deriving Repr, BEq, Inhabited

public meta inductive Quant where
  | all | no | some | lone | one
  deriving Repr, BEq, Inhabited

mutual

/-- `sig` keeps the resolved Lean name next to the sig string, so a stored
    spec still says which type it meant. -/
public meta inductive Sel where
  | sig (typeName : Name) (sig : String)
  | rel (name : String)
  | var (x : Name)
  | univ
  | iden
  | none_
  | atomLit (name : String)
  | union (a b : Sel)
  | diff (a b : Sel)
  | inter (a b : Sel)
  | prod (a b : Sel)
  | prodMult (a : Sel) (lm rm : Option ArrowMult) (b : Sel)
  | join (a b : Sel)
  | override (a b : Sel)
  | restrictDom (a b : Sel)
  | restrictRan (a b : Sel)
  | trans (a : Sel)
  | reflTrans (a : Sel)
  | transpose (a : Sel)
  | compr (binders : Array (Name × Sel)) (body : SelForm)
  /-- Escape hatch: an unchecked SGQ string, lowered verbatim. The body is
      arbitrary SGQ, so it binds loosest and composition parenthesizes it. -/
  | raw (sgq : String)
  deriving Repr, BEq

/-- Kept apart from `Sel` to reject SGQ's silent scalar/tuple confusion
    (`some #e`) at compile time. -/
public meta inductive SelInt where
  | lit (n : Int)
  | card (e : Sel)                                   -- `#e`
  | proj (e : Sel)                                   -- `@num:e`
  | builtin (op : IntBuiltin) (args : Array SelInt)  -- `add[a, b]`
  | agg (op : IntAgg) (e : Sel)                      -- `sum[e]`, `min[e]`, `max[e]`
  deriving Repr, BEq

/-- A nullary-constructor literal (`@:x = tt`) lowers to the short-name label
    the relationalizer gives its atoms. -/
public meta inductive SelVal where
  | label (proj : LabelProj) (e : Sel)
  | ctorLit (ctor : Name) (label : String)
  | strLit (s : String)
  | boolLit (b : Bool)
  deriving Repr, BEq

public meta inductive SelForm where
  | subset (a b : Sel)
  | notSubset (a b : Sel)
  /-- `a ni b` (reverse containment). -/
  | ni (a b : Sel)
  | notNi (a b : Sel)
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
  | ite (c t e : SelForm)  -- `a => b else c`
  | not (a : SelForm)
  | some_ (a : Sel)
  | no (a : Sel)
  | lone (a : Sel)
  | one (a : Sel)
  | quant (q : Quant) (disj : Bool) (binders : Array (Name × Sel)) (body : SelForm)
  deriving Repr, BEq

end

public meta instance : Inhabited Sel := ⟨.univ⟩
public meta instance : Inhabited SelInt := ⟨.lit 0⟩
public meta instance : Inhabited SelVal := ⟨.strLit ""⟩
public meta instance : Inhabited SelForm := ⟨.some_ .univ⟩

namespace Sel

/-- Forge's tight-end cascade (Expr8–Expr18), re-scaled. -/
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

/-- Mirrors `RESERVED_KEYWORDS` in simple-graph-query. -/
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

private meta def quoteIfReserved (s : String) : String :=
  if sgqReserved.contains s then s!"`{s}`" else s

/-- How SGQ spells `c` inside a double-quoted literal: these six escapes are
    the whole alphabet (any other backslash is dropped), everything else rides
    raw. `none` = no spelling at all (C0/DEL, which the JSON hop mangles). -/
private meta def sgqStringChar? : Char → Option String
  | '\\' => some "\\\\"
  | '"' => some "\\\""
  | '\n' => some "\\n"
  | '\t' => some "\\t"
  | '\r' => some "\\r"
  | '\x00' => some "\\0"
  | c => if c.val < 0x20 || c.val == 0x7f then none else some c.toString

/-- The first character of `s` that SGQ's string syntax cannot spell, for the
    elaborator to reject before it reaches a lowering. -/
public meta def sgqUnspellableChar? (s : String) : Option Char :=
  s.toList.find? fun c => (sgqStringChar? c).isNone

/-- Render `s` as an SGQ double-quoted string literal. An unspellable character
    rides raw — the elaborator has already rejected that case. -/
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

/-- `ctx` is the binding strength of the enclosing position. -/
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

public meta partial def SelInt.toSGQ : SelInt → String
  | .lit n => toString n
  -- 34: tighter than union/difference, looser than the rest (`#(a + b)`, bare `#a.b`)
  | .card e => s!"#{e.toSGQCtx 34}"
  | .proj e => s!"@num:{e.toSGQCtx 100}"
  | .builtin op args => s!"{op.toSGQ}[{", ".intercalate (args.toList.map SelInt.toSGQ)}]"
  -- Aggregators read numeric values; walker atom ids are opaque (`atom_N`),
  -- the value is the label — decode via the engine's numeric projection.
  | .agg op e => s!"{op.toSGQ}[@num:({e.toSGQCtx 0})]"

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

/-- Forge's loose-end cascade (`or` < `xor` < `iff` < `implies` < `and` <
    `not`); `implies` is right-associative. -/
public meta partial def SelForm.toSGQCtx (ctx : Nat) : SelForm → String
  | .subset a b => s!"{a.toSGQCtx 0} in {b.toSGQCtx 0}"
  | .notSubset a b => s!"{a.toSGQCtx 0} !in {b.toSGQCtx 0}"
  | .ni a b => s!"{a.toSGQCtx 0} ni {b.toSGQCtx 0}"
  | .notNi a b => s!"{a.toSGQCtx 0} !ni {b.toSGQCtx 0}"
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
  -- body extends maximally right; parenthesize under any connective
  | .quant q disj binders body =>
    let d := if disj then "disj " else ""
    parenIf (5 < ctx) s!"{q.toSGQ} {d}{bindersToSGQ binders (·.toSGQCtx 0)} | {body.toSGQ}"

public meta partial def SelForm.toSGQ (f : SelForm) : String := f.toSGQCtx 0

end

mutual

/-- Binders subtract positionally: a later binder's domain may reference an
    earlier binder. Lowering is name-based, so the elaborator uses this to
    reject a `let` substitution an inner binder would capture. -/
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

public meta partial def SelForm.freeVars : SelForm → Array Name
  | .subset a b | .notSubset a b | .ni a b | .notNi a b | .eq a b | .neq a b =>
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

public meta def Sel.toSGQ (s : Sel) : String := s.toSGQCtx 0

end SpytialLean

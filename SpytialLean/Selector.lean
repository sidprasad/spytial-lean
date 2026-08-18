module

public import Lean
public meta import SpytialLean.SelectorGenerated

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
  /-- Single binder, per Forge's expander. -/
  | sumQuant (x : Name) (dom : Sel) (body : SelInt)  -- `sum x : A | ie`
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

private meta def parenIf (needed : Bool) (s : String) : String :=
  if needed then s!"({s})" else s

/-! ## Rendering against the engine's cascade

`Sgq.Op` carries the level each operand slot descends to, so an operand is
parenthesized exactly when its own construct binds looser than its slot
accepts. Those levels are the engine's, not a local re-scaling: `+` takes its
right operand two levels in, which no single precedence number can say. -/

private meta def Sgq.Op.slot (o : Sgq.Op) (i : Nat) : Nat := o.operands[i]!

/-- `lhs op rhs`, with `sep` around the operator (empty for `.` and `->`). -/
private meta def infixSGQ (o : Sgq.Op) (ctx : Nat) (lhs rhs : Nat → String)
    (sep : String := " ") : String :=
  parenIf (o.prec < ctx) s!"{lhs (o.slot 0)}{sep}{o.text}{sep}{rhs (o.slot 1)}"

/-- A word-spelled operator would glue to its operand (`nota`), so it takes a
    space; a symbolic one (`^r`, `@num:e`) does not. The test is the engine's
    own bare-identifier rule, so it follows the spelling rather than a list. -/
private meta def gap (text : String) : String :=
  if Sgq.bareRest text.back then " " else ""

/-- `op operand`. Prefixes bind tightest and never need wrapping themselves. -/
private meta def prefixSGQ (o : Sgq.Op) (render : Nat → String) : String :=
  s!"{o.text}{gap o.text}{render (o.slot 0)}"

/-- `a !in b` and friends: the comparison's negation attaches to the operator
    rather than wrapping the formula. -/
private meta def negated (o : Sgq.Op) : Sgq.Op :=
  { o with text := Sgq.comparison.negation ++ o.text }

/-- Outside SGQ's bare-identifier rule the lexer fails open — `s₁` silently
    evaluates the prefix `s`, `σ` is a lexer error — so anything the rule does
    not cover is backquoted instead.

    FIXME: the empty name has no spelling at all (`Sgq.quoteMinLength` is 1),
    and this still emits the invalid `` `` `` for it. Nothing produces one
    today: sigs and relations come from resolved Lean names and binders from
    binder names. Fixing it properly means an error path through every caller. -/
private meta def quoteIfNeeded (s : String) : String :=
  let bare := match s.toList with
    | c :: cs => Sgq.bareHead c && cs.all Sgq.bareRest
    | [] => false
  if bare && s.length ≥ Sgq.bareMinLength && !Sgq.reserved.contains s then s
  else
    let esc := s.foldl (init := "") fun acc c =>
      if Sgq.quoteMustEscape.contains c then (acc.push Sgq.quoteEscape).push c else acc.push c
    s!"{Sgq.quoteDelimiter}{esc}{Sgq.quoteDelimiter}"

/-- How SGQ spells `c` inside a double-quoted literal. `none` = no spelling at
    all (C0/DEL without a readable escape, which the JSON hop mangles). -/
private meta def sgqStringChar? (c : Char) : Option String :=
  if let some spelled := Sgq.stringEscapeSpelling c then
    some s!"{Sgq.stringEscape}{spelled}"
  else if Sgq.stringMustEscape.contains c then
    some s!"{Sgq.stringEscape}{c}"
  else if c.val < 0x20 || c.val == 0x7f then none
  else some c.toString

/-- The first character of `s` that SGQ's string syntax cannot spell, for the
    elaborator to reject before it reaches a lowering. -/
public meta def sgqUnspellableChar? (s : String) : Option Char :=
  s.toList.find? fun c => (sgqStringChar? c).isNone

/-- Render `s` as an SGQ double-quoted string literal. An unspellable character
    rides raw — the elaborator has already rejected that case. -/
public meta def sgqStringLit (s : String) : String :=
  let body := s.toList.map fun c => (sgqStringChar? c).getD c.toString
  s!"{Sgq.stringDelimiter}{String.join body}{Sgq.stringDelimiter}"

private meta def ArrowMult.toSGQ : ArrowMult → String
  | .lone => "lone" | .one => "one" | .some => "some" | .set => "set"

/-- A builtin's SGQ name, checked against the list the engine dispatches on so
    a rename upstream is a build error rather than an unresolved call. -/
private meta def builtinNamed (available : List String) (name : String) : String :=
  if available.contains name then name
  else panic! s!"simple-graph-query no longer has the builtin `{name}`; run `just gen-sgq`"

private meta def IntBuiltin.toSGQ : IntBuiltin → String
  | .add => builtinNamed Sgq.binaryBuiltins "add"
  | .subtract => builtinNamed Sgq.binaryBuiltins "subtract"
  | .multiply => builtinNamed Sgq.binaryBuiltins "multiply"
  | .divide => builtinNamed Sgq.binaryBuiltins "divide"
  | .remainder => builtinNamed Sgq.binaryBuiltins "remainder"
  | .abs => builtinNamed Sgq.unaryBuiltins "abs"
  | .sign => builtinNamed Sgq.unaryBuiltins "sign"

private meta def IntAgg.toSGQ : IntAgg → String
  | .sum => builtinNamed Sgq.setBuiltins "sum"
  | .min => builtinNamed Sgq.setBuiltins "min"
  | .max => builtinNamed Sgq.setBuiltins "max"

private meta def IntCmp.toSGQ : IntCmp → String
  | .eq => Sgq.equal.text
  | .ne => Sgq.comparison.negation ++ Sgq.equal.text
  | .lt => Sgq.lessThan.text
  | .gt => Sgq.greaterThan.text
  | .le => Sgq.atMost.text
  | .ge => Sgq.atLeast.text

private meta def Quant.toSGQ : Quant → String
  | .all => Sgq.all.text | .no => Sgq.no.text | .some => Sgq.«some».text
  | .lone => Sgq.lone.text | .one => Sgq.one.text

private meta def bindersToSGQ (binders : Array (Name × Sel)) (domToSGQ : Sel → String) :
    String :=
  let groups := binders.foldl (init := #[]) fun (gs : Array (Array Name × Sel)) (x, dom) =>
    match gs.back? with
    | some (xs, dom') =>
      if dom' == dom then gs.set! (gs.size - 1) (xs.push x, dom') else gs.push (#[x], dom)
    | none => gs.push (#[x], dom)
  let sep := Sgq.quantifier.separator ++ " "
  sep.intercalate <| groups.toList.map fun (xs, dom) =>
    let names := sep.intercalate (xs.toList.map (quoteIfNeeded <| toString ·))
    s!"{names} {Sgq.quantifier.colon} {domToSGQ dom}"

mutual

/-- `ctx` is the level the enclosing position accepts. -/
public meta partial def Sel.toSGQCtx (ctx : Nat) : Sel → String
  | .sig _ s => quoteIfNeeded s
  | .rel r => quoteIfNeeded r
  | .var x => quoteIfNeeded (toString x)
  | .univ => Sgq.«universe».text
  | .iden => Sgq.identity.text
  | .none_ => Sgq.emptySet.text
  | .atomLit a => s!"{Sgq.atomLiteral.text}{a}"
  | .union a b => infixSGQ Sgq.union ctx a.toSGQCtx b.toSGQCtx
  | .diff a b => infixSGQ Sgq.difference ctx a.toSGQCtx b.toSGQCtx
  | .override a b => infixSGQ Sgq.override ctx a.toSGQCtx b.toSGQCtx
  | .inter a b => infixSGQ Sgq.intersection ctx a.toSGQCtx b.toSGQCtx
  | .prod a b => infixSGQ Sgq.product ctx a.toSGQCtx b.toSGQCtx (sep := "")
  | .prodMult a lm rm b =>
    let mul (m : Option ArrowMult) := match m with | some m => s!"{m.toSGQ} " | none => ""
    let o := Sgq.product
    parenIf (o.prec < ctx)
      s!"{a.toSGQCtx (o.slot 0)} {mul lm}{o.text} {mul rm}{b.toSGQCtx (o.slot 1)}"
  | .restrictDom a b => infixSGQ Sgq.domainRestriction ctx a.toSGQCtx b.toSGQCtx
  | .restrictRan a b => infixSGQ Sgq.rangeRestriction ctx a.toSGQCtx b.toSGQCtx
  | .join a b => infixSGQ Sgq.join ctx a.toSGQCtx b.toSGQCtx (sep := "")
  | .trans a => prefixSGQ Sgq.transitiveClosure a.toSGQCtx
  | .reflTrans a => prefixSGQ Sgq.reflexiveTransitiveClosure a.toSGQCtx
  | .transpose a => prefixSGQ Sgq.transpose a.toSGQCtx
  | .compr binders body =>
    let binders := bindersToSGQ binders (·.toSGQCtx Sgq.loosest)
    Sgq.comprehension.«open» ++ binders ++ " " ++ Sgq.comprehension.bar ++ " " ++
      body.toSGQ ++ Sgq.comprehension.close
  -- Raw SGQ is arbitrary, so it binds looser than anything the cascade names.
  | .raw s => parenIf (Sgq.loosest < ctx) s

public meta partial def SelInt.toSGQ : SelInt → String
  | .lit n => toString n
  | .card e => prefixSGQ Sgq.cardinality e.toSGQCtx
  | .proj e => prefixSGQ Sgq.labelNumber e.toSGQCtx
  | .builtin op args =>
    let sep := Sgq.application.separator ++ " "
    op.toSGQ ++ Sgq.application.«open» ++ sep.intercalate (args.toList.map SelInt.toSGQ) ++
      Sgq.application.close
  -- Aggregators read numeric values; walker atom ids are opaque (`atom_N`),
  -- the value is the label — decode via the engine's numeric projection.
  | .agg op e =>
    op.toSGQ ++ Sgq.application.«open» ++ Sgq.labelNumber.text ++
      s!"({e.toSGQCtx Sgq.loosest})" ++ Sgq.application.close
  -- the body extends maximally right; always wrap (`(sum …) > 2`)
  | .sumQuant x dom body =>
    s!"({Sgq.sum.text} {quoteIfNeeded (toString x)} {Sgq.quantifier.colon} " ++
      s!"{dom.toSGQCtx Sgq.loosest} {Sgq.quantifier.bar} {body.toSGQ})"

public meta partial def SelVal.toSGQ : SelVal → String
  | .label proj e =>
    let o := match proj with
      | .plain => Sgq.label | .str => Sgq.labelString | .bool => Sgq.labelBoolean
    prefixSGQ o e.toSGQCtx
  | .ctorLit _ label => sgqStringLit label
  -- The relationalizer labels a `String` atom with its Lean spelling, quotes
  -- included (`Relationalizer.lean`), so matching one takes a literal whose
  -- content carries those quotes too.
  | .strLit s => sgqStringLit s!"\"{s}\""
  | .boolLit b => toString b

/-- Formulas and relational expressions are one cascade in the engine, so both
    layers render against the same levels. -/
public meta partial def SelForm.toSGQCtx (ctx : Nat) : SelForm → String
  | .subset a b => infixSGQ Sgq.subset ctx a.toSGQCtx b.toSGQCtx
  | .notSubset a b => infixSGQ (negated Sgq.subset) ctx a.toSGQCtx b.toSGQCtx
  | .ni a b => infixSGQ Sgq.contains ctx a.toSGQCtx b.toSGQCtx
  | .notNi a b => infixSGQ (negated Sgq.contains) ctx a.toSGQCtx b.toSGQCtx
  | .eq a b => infixSGQ Sgq.equal ctx a.toSGQCtx b.toSGQCtx
  | .neq a b => infixSGQ (negated Sgq.equal) ctx a.toSGQCtx b.toSGQCtx
  | .veq a b => s!"{a.toSGQ} {Sgq.equal.text} {b.toSGQ}"
  | .vneq a b => s!"{a.toSGQ} {(negated Sgq.equal).text} {b.toSGQ}"
  | .icmp op a b => s!"{a.toSGQ} {op.toSGQ} {b.toSGQ}"
  | .or a b => infixSGQ Sgq.or ctx a.toSGQCtx b.toSGQCtx
  | .xor a b => infixSGQ Sgq.xor ctx a.toSGQCtx b.toSGQCtx
  | .iff a b => infixSGQ Sgq.iff ctx a.toSGQCtx b.toSGQCtx
  | .implies a b => infixSGQ Sgq.implies ctx a.toSGQCtx b.toSGQCtx
  | .ite c t e =>
    let o := Sgq.implies
    parenIf (o.prec < ctx)
      s!"{c.toSGQCtx (o.slot 0)} {o.text} {t.toSGQCtx (o.slot 1)} \
         {Sgq.implies.«else»} {e.toSGQCtx (o.slot 2)}"
  | .and a b => infixSGQ Sgq.and ctx a.toSGQCtx b.toSGQCtx
  | .not a => prefixSGQ Sgq.not a.toSGQCtx
  | .some_ a => prefixSGQ Sgq.nonEmpty a.toSGQCtx
  | .no a => prefixSGQ Sgq.empty a.toSGQCtx
  | .lone a => prefixSGQ Sgq.atMostOne a.toSGQCtx
  | .one a => prefixSGQ Sgq.exactlyOne a.toSGQCtx
  -- body extends maximally right; parenthesize under any connective
  | .quant q disj binders body =>
    let d := if disj then Sgq.quantifier.disjoint ++ " " else ""
    parenIf (Sgq.loosest < ctx)
      s!"{q.toSGQ} {d}{bindersToSGQ binders (·.toSGQCtx Sgq.loosest)} \
         {Sgq.quantifier.bar} {body.toSGQ}"

public meta partial def SelForm.toSGQ (f : SelForm) : String := f.toSGQCtx Sgq.loosest

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
  | .sumQuant x dom body => dom.freeVars ++ body.freeVars.filter (· != x)

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

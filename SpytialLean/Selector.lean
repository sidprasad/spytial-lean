module

public import Lean

namespace SpytialLean

open Lean

/-! # Selector — the reified SGQ expression language

The selector language spytial-core evaluates is the Forge expression language
(via the `simple-graph-query` ANTLR evaluator) extended with label-projection
operators (`@:`, `@str:`, `@bool:`, `@num:`). This module reifies the fragment
Spytial specs use as plain data: relational expressions (`Sel`), label/literal
values (`SelVal`), and formulas (`SelForm`, the bodies of set comprehensions).

The AST is what a `spytial_spec` stores in the environment (it must pickle into
`.olean`s), so nodes carry no `Syntax` — name resolution and checking happen in
the elaborator (`SpytialLean.SelectorElab`), which records resolved Lean names
here alongside the strings the relationalizer actually emits. Lowering back to
the concrete SGQ string consumed by spytial-core is `Sel.toSGQ`.
-/

/-- Which label projection a `SelVal.label` performs: `@:` reads an atom's label
    as a string; the typed variants coerce (`@str:`, `@bool:`, `@num:`). -/
public meta inductive LabelProj where
  | plain | str | bool | num
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
  | union (a b : Sel)
  | diff (a b : Sel)
  | inter (a b : Sel)
  | prod (a b : Sel)
  | join (a b : Sel)
  | trans (a : Sel)
  | reflTrans (a : Sel)
  | transpose (a : Sel)
  | compr (binders : Array (Name × Sel)) (body : SelForm)
  /-- Escape hatch: an unchecked SGQ string, lowered verbatim. For selectors
      whose vocabulary the checker cannot know (custom relationalizers,
      genuinely dynamic queries). -/
  | raw (sgq : String)
  deriving Repr, BEq

/-- A label/literal value, the operands of `@:`-style comparisons. A nullary
    constructor used as a literal (`@:x = tt`) resolves to the constructor and
    lowers to the label the relationalizer gives its atoms (the short name). -/
public meta inductive SelVal where
  | label (proj : LabelProj) (e : Sel)
  | ctorLit (ctor : Name) (label : String)
  | strLit (s : String)
  | numLit (n : Int)
  deriving Repr, BEq

/-- A formula — the body of a set comprehension. -/
public meta inductive SelForm where
  | subset (a b : Sel)
  | eq (a b : Sel)
  | neq (a b : Sel)
  | veq (a b : SelVal)
  | vneq (a b : SelVal)
  | and (a b : SelForm)
  | or (a b : SelForm)
  | implies (a b : SelForm)
  | not (a : SelForm)
  | some_ (a : Sel)
  | no (a : Sel)
  | lone (a : Sel)
  | one (a : Sel)
  deriving Repr, BEq

end

public meta instance : Inhabited Sel := ⟨.univ⟩
public meta instance : Inhabited SelVal := ⟨.strLit ""⟩
public meta instance : Inhabited SelForm := ⟨.some_ .univ⟩

namespace Sel

/-- Binding strength of a relational expression, mirroring Forge: union and
    difference bind loosest, then intersection, product, join; unary closure
    operators and atoms are tightest. -/
public meta def prec : Sel → Nat
  | union .. | diff .. => 30
  | inter .. => 40
  | prod .. => 50
  | join .. => 60
  | trans .. | reflTrans .. | transpose .. => 70
  | _ => 100

end Sel

private meta def parenIf (needed : Bool) (s : String) : String :=
  if needed then s!"({s})" else s

/-- How SGQ spells `c` inside a double-quoted literal. Its unquoting resolves
    exactly `\n`, `\t`, `\r`, `\0`, `\"` and `\\` and drops the backslash from
    every other escape, so those six are the whole escape alphabet and any other
    character has to ride raw. `none` marks a character with no spelling either
    way: a C0 control or DEL without an escape of its own, which would have to
    ride raw through the spec's JSON hop and does not survive it. -/
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

mutual

/-- `ctx` is the binding strength of the enclosing position. -/
public meta partial def Sel.toSGQCtx (ctx : Nat) : Sel → String
  | .sig _ s => s
  | .rel r => r
  | .var x => toString x
  | .univ => "univ"
  | .iden => "iden"
  | e@(.union a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 30} + {b.toSGQCtx 31}"
  | e@(.diff a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 30} - {b.toSGQCtx 31}"
  | e@(.inter a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 40} & {b.toSGQCtx 41}"
  | e@(.prod a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 50}->{b.toSGQCtx 51}"
  | e@(.join a b) => parenIf (e.prec < ctx) s!"{a.toSGQCtx 60}.{b.toSGQCtx 61}"
  | .trans a => s!"^{a.toSGQCtx 71}"
  | .reflTrans a => s!"*{a.toSGQCtx 71}"
  | .transpose a => s!"~{a.toSGQCtx 71}"
  | .compr binders body =>
    -- Adjacent binders of one domain print grouped: `{x, y : BDD | ...}`.
    let groups := binders.foldl (init := #[]) fun (gs : Array (Array Name × Sel)) (x, dom) =>
      match gs.back? with
      | some (xs, dom') =>
        if dom' == dom then gs.set! (gs.size - 1) (xs.push x, dom') else gs.push (#[x], dom)
      | none => gs.push (#[x], dom)
    let binderStr := ", ".intercalate <| groups.toList.map fun (xs, dom) =>
      let names := ", ".intercalate (xs.toList.map toString)
      s!"{names} : {dom.toSGQCtx 0}"
    s!"\{{binderStr} | {body.toSGQ}}"
  | .raw s => s

/-- Lower a value operand. The projected expression prints at atom strength, so
    `@:x` stays bare while `@:(x.v)` gets its parentheses. -/
public meta partial def SelVal.toSGQ : SelVal → String
  | .label proj e =>
    let tok := match proj with
      | .plain => "@:"
      | .str => "@str:"
      | .bool => "@bool:"
      | .num => "@num:"
    s!"{tok}{e.toSGQCtx 100}"
  | .ctorLit _ label => sgqStringLit label
  -- The relationalizer labels a `String` atom with its Lean spelling, quotes
  -- included (`Relationalizer.lean`), so matching one takes a literal whose
  -- content carries those quotes too.
  | .strLit s => sgqStringLit s!"\"{s}\""
  | .numLit n => toString n

/-- Lower a formula. Connective precedence: `implies` loosest, then `or`,
    `and`, `not`; atomic comparisons need no parenthesization decisions. -/
public meta partial def SelForm.toSGQCtx (ctx : Nat) : SelForm → String
  | .subset a b => s!"{a.toSGQCtx 0} in {b.toSGQCtx 0}"
  | .eq a b => s!"{a.toSGQCtx 0} = {b.toSGQCtx 0}"
  | .neq a b => s!"{a.toSGQCtx 0} != {b.toSGQCtx 0}"
  | .veq a b => s!"{a.toSGQ} = {b.toSGQ}"
  | .vneq a b => s!"{a.toSGQ} != {b.toSGQ}"
  | .implies a b => parenIf (10 < ctx) s!"{a.toSGQCtx 11} implies {b.toSGQCtx 10}"
  | .or a b => parenIf (20 < ctx) s!"{a.toSGQCtx 20} or {b.toSGQCtx 21}"
  | .and a b => parenIf (30 < ctx) s!"{a.toSGQCtx 30} and {b.toSGQCtx 31}"
  | .not a => s!"not {a.toSGQCtx 40}"
  | .some_ a => s!"some {a.toSGQCtx 0}"
  | .no a => s!"no {a.toSGQCtx 0}"
  | .lone a => s!"lone {a.toSGQCtx 0}"
  | .one a => s!"one {a.toSGQCtx 0}"

public meta partial def SelForm.toSGQ (f : SelForm) : String := f.toSGQCtx 0

end

/-- Lower a selector to the concrete SGQ string spytial-core evaluates. -/
public meta def Sel.toSGQ (s : Sel) : String := s.toSGQCtx 0

end SpytialLean

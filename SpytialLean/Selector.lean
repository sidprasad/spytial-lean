module

public import Lean
public meta import SpytialLean.Sgq

namespace SpytialLean

open Lean

/-! # Selector — SGQ expressions as data

A selector is one of simple-graph-query's expressions. This module reifies
them and lowers them back to the concrete syntax spytial-core evaluates.

Nothing here names a construct. A node carries the manifest's construct id, the
operator written, and the pieces its production has, in the order the
production has them (`Sgq.Construct.template`); rendering walks that template.
So a construct added upstream reaches the lowering by rebuilding, with no
edit here.

What is *not* the engine's, and so is written here: the vocabulary leaves
(`sig`/`rel`/`var` are resolved Lean names, not bare identifiers), the
constructor-label literal a spytial spec compares against, the `raw` escape
hatch, and the whitespace house style.

Specs store this AST in the environment, so nodes carry no `Syntax` and must
pickle into `.olean`s. `SpytialLean.SelectorElab` resolves and checks; `toSGQ`
lowers.
-/

mutual

/-- One filled position of a production, in `template` order. Positions with a
    fixed spelling carry nothing and are absent. -/
public meta inductive Arg where
  /-- An operand, a body, or the domain of a bracket. -/
  | expr (e : Sel)
  /-- An argument list (`f[a, b]`) or a block's conjuncts. -/
  | exprs (es : Array Sel)
  /-- Binder groups, one entry per name; adjacent equal domains regroup when
      rendered, so `x, y : S` survives the round trip. -/
  | binders (bs : Array (Name × Sel))
  /-- A bare-name position (`` `a0 ``, `@x`). -/
  | name (s : String)
  /-- An optional part: the spelling written, or `none` for absent. -/
  | atom (spelling : Option String)
  deriving Repr, BEq

public meta inductive Sel where
  /-- An instance of a manifest construct. `op` is the operator written, absent
      for a construct that has none (a comprehension, a bracket). -/
  | node (construct : Sgq.ConstructId) (op : Option Sgq.OpId) (args : Array Arg)
  /-- A type reference. Keeps the resolved Lean name next to the sig string, so
      a stored spec still says which type it meant. -/
  | sig (typeName : Name) (sig : String)
  | rel (name : String)
  /-- One of the engine's named builtins (`add`, `sum`). A separate vocabulary
      from the relations: `sum` is a reserved word that `quoteIfNeeded` would
      backquote, and the grammar admits it bare in exactly this position. -/
  | builtin (name : String)
  | var (x : Name)
  | num (n : Int)
  | str (s : String)
  /-- A nullary-constructor literal (`@:x = tt`), which lowers to the
      short-name label the relationalizer gives its atoms. -/
  | ctorLit (ctor : Name) (label : String)
  | boolLit (b : Bool)
  /-- Escape hatch: an unchecked SGQ string, lowered verbatim. The body is
      arbitrary SGQ, so it binds loosest and composition parenthesizes it. -/
  | raw (sgq : String)
  deriving Repr, BEq

end

public meta instance : Inhabited Sel := ⟨.raw ""⟩
public meta instance : Inhabited Arg := ⟨.atom none⟩

/-! ## Names and literals

Outside SGQ's bare-identifier rule the lexer fails open — `s₁` silently
evaluates the prefix `s`, `σ` is a lexer error — so anything the rule does not
cover is backquoted instead. -/

/-- Whether `s` is spelled the way the engine's lexer spells a bare name. Both
    ends of the language need this: the encoder to decide what to quote, the
    parser to decide whether a spelling is a keyword or an identifier. -/
public meta def sgqBareName (s : String) : Bool :=
  match s.toList with
  | c :: cs => Sgq.bareHead c && cs.all Sgq.bareRest
  | [] => false

/-- A builtin's name, checked against the engine's own lists so a rename
    upstream is a loud failure rather than an unresolved call at render.
    `tests/SgqCoverageTest.lean` makes the same mismatch a build failure; this
    is the backstop for a name that reaches the lowering anyway. -/
public meta def sgqBuiltin (name : String) : String :=
  if (Sgq.binaryBuiltins ++ Sgq.unaryBuiltins ++ Sgq.setBuiltins).contains name then name
  else panic! s!"simple-graph-query no longer spells `{name}`; this call site is stale"

/-- FIXME: the empty name has no spelling at all (`Sgq.quoteMinLength` is 1),
    and this still emits the invalid `` `` `` for it. Nothing produces one
    today: sigs and relations come from resolved Lean names and binders from
    binder names. Fixing it properly means an error path through every caller. -/
public meta def quoteIfNeeded (s : String) : String :=
  if sgqBareName s && s.length ≥ Sgq.bareMinLength && !Sgq.reserved.contains s then s
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

/-! ## Whitespace

Both spacings parse — the engine's lexer skips whitespace between every token —
so this is house style, not a language fact. It is stated as two tables over
the generated enumerations rather than per construct, so a construct added
upstream is formatted without an edit, and a *role* added upstream is a
non-exhaustive match rather than a silent default. -/

public meta structure Air where
  /-- Air before this chunk. -/
  left : Bool := false
  /-- Air after it. -/
  right : Bool := false
  /-- Suppress the next chunk's own `left`: `!` binds onto its comparison, so
      `a !in b` rather than `a ! in b`. -/
  glueRight : Bool := false

/-- Infix operators written without air. Everything else takes it, so `a + b`
    and `a in b` but `a.b` and `a->b`. -/
private meta def tightInfix : List Sgq.OpId := [.«join», .«product»]

private meta def roleAir : Sgq.Role → Air
  | .«negation» => { left := true, glueRight := true }
  | .«colon» | .«bar» | .«bind» | .«else» | .«disjoint» | .«domainMultiplicity»
  | .«multiplicity» => { left := true, right := true }
  | .«separator» => { right := true }
  | .«open» | .«close» | .«blockOpen» | .«blockClose» => {}

/-- A word-spelled operator would run into its neighbour (`nota`, `some\`x\``),
    so it takes air on whichever side is a bare-name character; a symbolic one
    does not. An infix operator takes air on both sides unless it is one of the
    tight ones — and even then, only while nothing else is written beside it:
    `a->b`, but `a one -> lone b`. -/
private meta def opAir (o : Sgq.Op) (beside : Bool) : Air :=
  if (Sgq.Construct.of o.construct).fixity == .«infix» &&
      (beside || !tightInfix.contains o.id) then
    { left := true, right := true }
  else { left := Sgq.bareHead o.text.front, right := Sgq.bareRest o.text.back }

/-- Whether writing `l` and `r` adjacently would lex differently from writing
    them apart: two bare-name runs would merge into one name, or some lexeme
    would span the boundary. Over-approximates — a space is always safe and a
    missing one is not — so it is a floor under the house style above, and
    `not a` needs no entry in either table. -/
private meta def glues (l r : String) : Bool :=
  if l.isEmpty || r.isEmpty then false
  else if Sgq.bareRest l.back && Sgq.bareRest r.front then true
  else Sgq.lexemes.any fun t =>
    1 < t.length && (List.range (min (t.length - 1) l.length)).any fun k =>
      t.startsWith (l.drop (l.length - (k + 1))) && r.startsWith (t.drop (k + 1))

private meta def assemble (chunks : Array (String × Air)) : String := Id.run do
  let mut out := ""
  let mut prev : Air := {}
  for (t, air) in chunks do
    if t.isEmpty then continue
    if !out.isEmpty then
      if prev.right || (air.left && !prev.glueRight) || glues out t then
        out := out ++ " "
    out := out ++ t
    prev := air
  return out

/-- The argument filling template position `i`. A node is built by the
    elaborator against the same template that renders it, so a short argument
    array is a bug in one of the two; say which construct rather than panicking
    on a bare index. -/
private meta def argAt (cd : Sgq.Construct) (args : Array Arg) (i : Nat) : Arg :=
  args[i]?.getD <| panic!
    s!"{Sgq.constructName cd.id}: template position {i} has no argument \
       ({args.size} given)"

private meta def parenIf (needed : Bool) (s : String) : String :=
  if needed then s!"({s})" else s

/-! ## Lowering

`Sgq.Construct.template` gives the production in source order, each operand
position carrying the cascade level it descends to, so an operand is
parenthesized exactly when its own construct binds looser than its slot
accepts. Those levels are the engine's, not a local re-scaling: `+` takes its
right operand two levels in, which no single precedence number can say. -/

mutual

/-- `ctx` is the level the enclosing position accepts. -/
public meta partial def Sel.toSGQCtx (ctx : Nat) : Sel → String
  | .sig _ s => quoteIfNeeded s
  | .rel r => quoteIfNeeded r
  | .builtin b => sgqBuiltin b
  | .var x => quoteIfNeeded (toString x)
  | .num n => toString n
  -- The relationalizer labels a `String` atom with its Lean spelling, quotes
  -- included (`Relationalizer.lean`), so matching one takes a literal whose
  -- content carries those quotes too.
  | .str s => sgqStringLit s!"\"{s}\""
  | .ctorLit _ label => sgqStringLit label
  | .boolLit b => toString b
  -- Raw SGQ is arbitrary, so it binds looser than anything the cascade names.
  | .raw s => parenIf (Sgq.loosest < ctx) s
  | .node c op args =>
    let cd := Sgq.Construct.of c
    parenIf (cd.prec < ctx) (assemble (renderItems cd op cd.template args 0).1)

/-- Walks a template against the arguments that fill it, returning the chunks
    and how many arguments were consumed. -/
private meta partial def renderItems (cd : Sgq.Construct) (op : Option Sgq.OpId)
    (items : List Sgq.Item) (args : Array Arg) (start : Nat) :
    Array (String × Air) × Nat := Id.run do
  let mut out : Array (String × Air) := #[]
  let mut i := start
  let beside := args.any fun a => match a with | .atom (some _) => true | _ => false
  let expr (a : Arg) (level : Nat) : String :=
    match a with | .expr e => e.toSGQCtx level | _ => ""
  for item in items do
    match item with
    | .operand level =>
      out := out.push (expr (argAt cd args i) level, {})
      i := i + 1
    | .body level =>
      out := out.push (cd.part .«bar» |>.text, roleAir .«bar»)
      out := out.push (expr (argAt cd args i) level, {})
      i := i + 1
    | .«repeat» level =>
      if let .exprs es := (argAt cd args i) then
        for e in es do out := out.push (e.toSGQCtx level, { left := true, right := true })
      i := i + 1
    | .list level role =>
      if let .exprs es := (argAt cd args i) then
        for (e, n) in es.zipIdx do
          if n != 0 then out := out.push (cd.part role |>.text, roleAir role)
          out := out.push (e.toSGQCtx level, {})
      i := i + 1
    | .binders typed level =>
      if let .binders bs := (argAt cd args i) then out := out ++ renderBinders cd typed level bs
      i := i + 1
    | .name _ =>
      if let .name s := (argAt cd args i) then out := out.push (quoteIfNeeded s, {})
      i := i + 1
    | .operator | .constant =>
      -- `constant` is the `const` alternation; the numeric and string literals
      -- it also spells are `Sel` leaves of their own, so a node here is always
      -- one of its named constants.
      if let some o := op then
        let od := Sgq.Op.of o
        out := out.push (od.text, opAir od beside)
    | .part role optional =>
      if optional then
        -- Aliases write house style; alternatives write what the source chose.
        let part := cd.part role
        if let .atom (some s) := (argAt cd args i) then
          out := out.push (if part.alternatives then s else part.text, roleAir role)
        i := i + 1
      else
        out := out.push (cd.part role |>.text, roleAir role)
    | .«optional» inner =>
      let present := match (argAt cd args i) with | .atom s => s.isSome | _ => false
      i := i + 1
      if present then
        let (chunks, next) := renderItems cd op inner args i
        out := out ++ chunks
        i := next
  return (out, i)

/-- `x, y : dom` for a quantifier or comprehension, `x = e` for a `let`.
    Adjacent binders over the same domain regroup, so the source form survives
    the round trip. -/
private meta partial def renderBinders (cd : Sgq.Construct) (typed : Bool) (level : Nat)
    (bs : Array (Name × Sel)) : Array (String × Air) := Id.run do
  let sep := (cd.part .«separator», roleAir .«separator»)
  let groups := if !typed then bs.map (fun b => (#[b.1], b.2)) else
    bs.foldl (init := #[]) fun (gs : Array (Array Name × Sel)) (x, dom) =>
      match gs.back? with
      | some (xs, dom') =>
        if dom' == dom then gs.set! (gs.size - 1) (xs.push x, dom') else gs.push (#[x], dom)
      | none => gs.push (#[x], dom)
  let mut out : Array (String × Air) := #[]
  for ((xs, dom), n) in groups.zipIdx do
    if n != 0 then out := out.push (sep.1.text, sep.2)
    for (x, m) in xs.zipIdx do
      if m != 0 then out := out.push (sep.1.text, sep.2)
      out := out.push (quoteIfNeeded (toString x), {})
    let role := if typed then Sgq.Role.«colon» else .«bind»
    out := out.push (cd.part role |>.text, roleAir role)
    out := out.push (dom.toSGQCtx level, {})
  return out

end

public meta def Sel.toSGQ (s : Sel) : String := s.toSGQCtx Sgq.loosest

/-! ## Free variables

Binders subtract positionally: a later binder's domain may reference an earlier
binder, and the body sees them all. Template order puts the binder positions
before the body, so one left-to-right pass is the whole rule. Lowering is
name-based, so the elaborator uses this to reject a `let` substitution an inner
binder would capture. -/

public meta partial def Sel.freeVars : Sel → Array Name
  | .var x => #[x]
  | .sig .. | .rel .. | .builtin .. | .num .. | .str .. | .ctorLit .. | .boolLit ..
  | .raw .. => #[]
  | .node _ _ args => Id.run do
    let mut bound : Array Name := #[]
    let mut out : Array Name := #[]
    let free (e : Sel) (bound : Array Name) := e.freeVars.filter (!bound.contains ·)
    for a in args do
      match a with
      | .expr e => out := out ++ free e bound
      | .exprs es => for e in es do out := out ++ free e bound
      | .binders bs =>
        for (x, dom) in bs do
          out := out ++ free dom bound
          bound := bound.push x
      | .name _ | .atom _ => pure ()
    return out

end SpytialLean

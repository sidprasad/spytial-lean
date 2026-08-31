module

public import Lean
public meta import SpytialLean.Sgq
public meta import SpytialLean.TypeShape

namespace SpytialLean

open Lean

/-! # Selector — SGQ expressions as data

"The engine", here and in the modules below, is simple-graph-query. Nothing here
names a construct: a node carries the manifest's construct id, the operator
written, and its production's pieces in template order, so a construct added
upstream reaches the lowering by rebuilding. Specs store this AST in the
environment, so nodes must pickle into `.olean`s and carry no `Syntax`. -/

mutual

/-- One filled position of a production, in `template` order. Positions with a
    fixed spelling carry nothing and are absent. -/
public meta inductive Arg where
  | expr (e : Sel)
  | exprs (es : Array Sel)
  /-- One entry per name, not per group. -/
  | binders (bs : Array (Name × Sel))
  | name (s : String)
  | atom (spelling : Option String)
  deriving Repr, BEq

public meta inductive Sel where
  /-- `op` is absent for a construct that has none (a comprehension, a bracket). -/
  | node (construct : Sgq.ConstructId) (op : Option Sgq.OpId) (args : Array Arg)
  /-- The Lean name rides along so a stored spec still says which type it meant. -/
  | sig (typeName : Name) (sig : String)
  | rel (name : String)
  /-- Its own vocabulary: `sum` is a reserved word `quoteIfNeeded` would
      backquote, but the grammar admits it bare in exactly this position. -/
  | builtin (name : String)
  | var (x : Name)
  | num (n : Int)
  | str (s : String)
  | ctorLit (ctor : Name)
  | boolLit (b : Bool)
  /-- A raw Lean function read as a relation: its argument types are the columns,
      its codomain the arity (`classifyLeanRel`). `resolveLeanSelectors` rewrites
      it to the tuples it selects before anything lowers to SGQ. -/
  | leanRel (fn : Expr)
  deriving Repr, BEq

end

public meta instance : Inhabited Sel := ⟨.num 0⟩
public meta instance : Inhabited Arg := ⟨.atom none⟩

/-- Fills only operand and optional positions; a production with a name, a list,
    binders or a body gets a node with no lowering rather than a guessed one. -/
public meta def Sel.op (o : Sgq.OpId) (operands : Array Sel) : Sel :=
  let cd := Sgq.Construct.of (Sgq.Op.of o).construct
  let (args, _) := cd.template.foldl (init := (#[], 0)) fun (acc, n) item =>
    match item with
    | .operand _ => (match operands[n]? with | some e => acc.push (Arg.expr e) | none => acc,
        n + 1)
    | .part _ true | .«optional» _ => (acc.push (Arg.atom none), n)
    | _ => (acc, n)
  .node cd.id (some o) args

public meta def Sel.atomLit (id : String) : Sel :=
  .node .«atomLiteral» (some .«atomLiteral») #[.name id]

public meta def Sel.empty : Sel := Sel.op .«emptySet» #[]

/-! ## Names and literals -/

public meta def sgqBareName (s : String) : Bool :=
  match s.toList with
  | c :: cs => Sgq.bareHead c && cs.all Sgq.bareRest
  | [] => false

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

/-- `none` = no spelling at all (C0/DEL without a readable escape, which the
    JSON hop mangles). -/
private meta def sgqStringChar? (c : Char) : Option String :=
  if let some spelled := Sgq.stringEscapeSpelling c then
    some s!"{Sgq.stringEscape}{spelled}"
  else if Sgq.stringMustEscape.contains c then
    some s!"{Sgq.stringEscape}{c}"
  else if c.val < 0x20 || c.val == 0x7f then none
  else some c.toString

public meta def sgqUnspellableChar? (s : String) : Option Char :=
  s.toList.find? fun c => (sgqStringChar? c).isNone

/-- An unspellable character rides raw; the elaborator rejects that first. -/
public meta def sgqStringLit (s : String) : String :=
  let body := s.toList.map fun c => (sgqStringChar? c).getD c.toString
  s!"{Sgq.stringDelimiter}{String.join body}{Sgq.stringDelimiter}"

/-! ## Whitespace -/

/-- The engine's lexer skips whitespace between every token, so every spacing
    below is this package's choice, not a language fact. -/
public meta structure Air where
  left : Bool := false
  right : Bool := false
  /-- Suppress the next chunk's own `left`: `!` binds onto its comparison, so
      `a !in b` rather than `a ! in b`. -/
  glueRight : Bool := false

private meta def tightInfix : List Sgq.OpId := [.«join», .«product»]

private meta def roleAir : Sgq.Role → Air
  | .«negation» => { left := true, glueRight := true }
  | .«colon» | .«bar» | .«bind» | .«else» | .«disjoint» | .«domainMultiplicity»
  | .«multiplicity» => { left := true, right := true }
  | .«separator» => { right := true }
  | .«open» | .«close» | .«blockOpen» | .«blockClose» => {}

/-- `beside` says some optional part is written beside the operator, which
    unglues even a tight infix: `a->b`, but `a one -> lone b`. -/
private meta def opAir (o : Sgq.Op) (beside : Bool) : Air :=
  if (Sgq.Construct.of o.construct).fixity == .«infix» &&
      (beside || !tightInfix.contains o.id) then
    { left := true, right := true }
  else { left := Sgq.bareHead o.text.front, right := Sgq.bareRest o.text.back }

/-- Whether `l` and `r` written adjacently would lex differently from apart.
    Over-approximates, so it is a safe floor under the spacing tables above. -/
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

/-- A node is built against the same template that renders it, so a missing or
    wrong-kind argument is a bug in one of the two; the node then has no
    lowering at all, rather than one with the position silently dropped. -/
private meta def argAt (cd : Sgq.Construct) (args : Array Arg) (i : Nat) :
    Except String Arg :=
  match args[i]? with
  | some a => .ok a
  | none => .error s!"{Sgq.constructName cd.id}: template position {i} has no \
      argument ({args.size} given)"

private meta def Arg.what : Arg → String
  | .expr _ => "an expression"
  | .exprs _ => "an expression list"
  | .binders _ => "binder groups"
  | .name _ => "a name"
  | .atom _ => "an optional part"

private meta def wrongArg {α : Type} (cd : Sgq.Construct) (i : Nat) (want : String)
    (got : Arg) : Except String α :=
  .error s!"{Sgq.constructName cd.id}: template position {i} takes {want}, \
    got {got.what}"

private meta def parenIf (needed : Bool) (s : String) : String :=
  if needed then s!"({s})" else s

/-! ## Lowering -/

mutual

/-- `ctx` is the level the enclosing position accepts. -/
public meta partial def Sel.toSGQCtx (ctx : Nat) : Sel → Except String String
  | .sig _ s => .ok (quoteIfNeeded s)
  | .builtin b => .ok b
  | .rel r => .ok (quoteIfNeeded r)
  | .var x => .ok (quoteIfNeeded (toString x))
  | .num n => .ok (toString n)
  -- The relationalizer labels a `String` atom with its Lean spelling, quotes
  -- included, so matching one takes a literal that carries those quotes too.
  | .str s => .ok (sgqStringLit s!"\"{s}\"")
  | .ctorLit c => .ok (sgqStringLit (shortName c))
  | .boolLit b => .ok (toString b)
  | .leanRel _ => Sel.empty.toSGQCtx ctx
  | .node c op args => do
    let cd := Sgq.Construct.of c
    return parenIf (cd.prec < ctx) (assemble (← renderItems cd op cd.template args 0).1)

private meta partial def renderItems (cd : Sgq.Construct) (op : Option Sgq.OpId)
    (items : List Sgq.Item) (args : Array Arg) (start : Nat) :
    Except String (Array (String × Air) × Nat) := do
  let mut out : Array (String × Air) := #[]
  let mut i := start
  let beside := args.any fun a => match a with | .atom (some _) => true | _ => false
  let expr (pos : Nat) (a : Arg) (level : Nat) : Except String String :=
    match a with | .expr e => e.toSGQCtx level | _ => wrongArg cd pos "an expression" a
  for item in items do
    match item with
    | .operand level =>
      out := out.push (← expr i (← argAt cd args i) level, {})
      i := i + 1
    | .body level =>
      out := out.push (cd.part .«bar» |>.text, roleAir .«bar»)
      out := out.push (← expr i (← argAt cd args i) level, {})
      i := i + 1
    | .«repeat» level =>
      let a ← argAt cd args i
      let .exprs es := a | wrongArg cd i "an expression list" a
      for e in es do out := out.push (← e.toSGQCtx level, { left := true, right := true })
      i := i + 1
    | .list level role =>
      let a ← argAt cd args i
      let .exprs es := a | wrongArg cd i "an expression list" a
      for (e, n) in es.zipIdx do
        if n != 0 then out := out.push (cd.part role |>.text, roleAir role)
        out := out.push (← e.toSGQCtx level, {})
      i := i + 1
    | .binders typed level =>
      let a ← argAt cd args i
      let .binders bs := a | wrongArg cd i "binder groups" a
      out := out ++ (← renderBinders cd typed level bs)
      i := i + 1
    | .name _ =>
      let a ← argAt cd args i
      let .name s := a | wrongArg cd i "a name" a
      out := out.push (quoteIfNeeded s, {})
      i := i + 1
    | .operator | .constant =>
      if let some o := op then
        let od := Sgq.Op.of o
        out := out.push (od.text, opAir od beside)
    | .part role optional =>
      if optional then
        let a ← argAt cd args i
        let .atom spelling := a | wrongArg cd i "an optional part" a
        if let some s := spelling then
          let part := cd.part role
          out := out.push (if part.alternatives then s else part.text, roleAir role)
        i := i + 1
      else
        out := out.push (cd.part role |>.text, roleAir role)
    | .«optional» inner =>
      let a ← argAt cd args i
      let .atom spelling := a | wrongArg cd i "an optional part" a
      let present := spelling.isSome
      i := i + 1
      if present then
        let (chunks, next) ← renderItems cd op inner args i
        out := out ++ chunks
        i := next
  return (out, i)

/-- Adjacent binders over the same domain regroup, for round-trip fidelity. -/
private meta partial def renderBinders (cd : Sgq.Construct) (typed : Bool) (level : Nat)
    (bs : Array (Name × Sel)) : Except String (Array (String × Air)) := do
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
    out := out.push (← dom.toSGQCtx level, {})
  return out

end

public meta def Sel.toSGQ (s : Sel) : Except String String := s.toSGQCtx Sgq.loosest

/-- Binders subtract positionally: template order puts the binder positions
    before the body, so one left-to-right pass is the whole rule. -/
public meta partial def Sel.freeVars : Sel → Array Name
  | .var x => #[x]
  | .sig .. | .rel .. | .builtin .. | .num .. | .str .. | .ctorLit .. | .boolLit ..
  | .leanRel .. => #[]
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

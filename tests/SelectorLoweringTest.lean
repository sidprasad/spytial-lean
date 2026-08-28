module

public import Lean
public meta import SpytialLean.Selector

open SpytialLean Lean

/-! # SGQ lowering goldens

`Selector.lean` renders through the `Sgq` tables, derived at elaboration from
simple-graph-query's manifest, so a changed operand level upstream silently
changes every spec this package writes. The spec goldens in `SelectorTest.lean`
cover the shapes the surface DSL spells, which leaves the precedence matrix and
the awkward names unpinned.

The corpus is systematic, and its operator lists come from the manifest rather
than from a copy of it: every relational binary against every other nested both
ways, every unary over and under every binary, every connective pair, every
comparison negated and not, the multiplicity grid, the names SGQ cannot spell
bare. An operator added upstream enters the corpus without an edit here, and
shows up as new golden lines.

Each case was checked against simple-graph-query's own parser when the table was
written: see `tests/README-lowering.md` for the differential rig. Four cases are
`/`-named relations that lowering emits unquoted (which does not parse), two are
raw fragments left unbracketed (which parse as a different formula), and four
are the empty relation name, which SGQ cannot spell at all — see
`quoteIfNeeded`'s FIXME.

After a deliberate change, `just rebless-sgq` rewrites the golden. -/

/-! ## Building nodes

A node is a construct id, the operator written, and one argument per template
position that carries something. These are the handful of shapes the corpus
uses, spelled once. -/

private meta def constructOf (o : Sgq.OpId) : Sgq.ConstructId := (Sgq.Op.of o).construct

/-- Fills an operator's template: the given operands in order, every optional
    part absent. Template-driven like the elaborator, so a construct that grows
    a slot cannot leave these builders short. -/
private meta def node (o : Sgq.OpId) (operands : Array Sel) : Sel :=
  let cd := Sgq.Construct.of (constructOf o)
  let (args, _) := cd.template.foldl (init := (#[], 0)) fun (acc, n) item =>
    match item with
    | .operand _ => (acc.push (Arg.expr operands[n]!), n + 1)
    | .part _ true | .«optional» _ => (acc.push (Arg.atom none), n)
    | _ => (acc, n)
  .node cd.id (some o) args

private meta def nullary (o : Sgq.OpId) : Sel := node o #[]
private meta def unary (o : Sgq.OpId) (x : Sel) : Sel := node o #[x]
private meta def binary (o : Sgq.OpId) (x y : Sel) : Sel := node o #[x, y]
/-- The negation is a slot of the comparison, not an operator of its own. -/
private meta def cmp (o : Sgq.OpId) (neg : Bool) (x y : Sel) : Sel :=
  .node .«comparison» (some o) #[.expr x, .atom (if neg then some "!" else none), .expr y]
private meta def prod (lm rm : Option String) (x y : Sel) : Sel :=
  .node .«product» (some .«product») #[.expr x, .atom lm, .atom rm, .expr y]
private meta def quant (o : Sgq.OpId) (disj : Bool) (bs : Array (Name × Sel)) (body : Sel) : Sel :=
  .node .«quantifier» (some o)
    #[.atom (if disj then some "disj" else none), .binders bs, .expr body]
private meta def compr (bs : Array (Name × Sel)) (body : Sel) : Sel :=
  .node .«comprehension» none #[.binders bs, .expr body]
private meta def call (f : String) (xs : Array Sel) : Sel :=
  .node .«application» none #[.expr (.builtin f), .exprs xs]
private meta def boxJoin (f : Sel) (xs : Array Sel) : Sel :=
  .node .«application» none #[.expr f, .exprs xs]
private meta def atomLit (n : String) : Sel :=
  .node .«atomLiteral» (some .«atomLiteral») #[.name n]
private meta def implies (c t : Sel) (e : Option Sel) : Sel :=
  .node .«implies» (some .«implies»)
    (#[Arg.expr c, .expr t, .atom (e.map fun _ => "else")] ++
      (e.toArray.map Arg.expr))

/-! ## Which operators the corpus ranges over

Read off the manifest by shape, so a new operator is covered rather than
missed. -/

private meta def opsWhere (p : Sgq.Op → Bool) : List Sgq.OpId :=
  Sgq.allOps.filter fun o => let od := Sgq.Op.of o; od.evaluates && p od

private meta def fixityOf (o : Sgq.Op) : Sgq.Fixity := (Sgq.Construct.of o.construct).fixity
/-- `n` operand slots, each accepting `k`. The count matters: `\`a0` is a
    prefix over no operand at all, so it is not one of the unaries. -/
private meta def takes (o : Sgq.Op) (n : Nat) (k : Sgq.Kind) : Bool :=
  o.kinds.operands.length == n && o.kinds.operands.all (· == some k)

/-- The relational binaries: `+`, `.`, `->`, `<:`, … -/
private meta def relBinaries : List Sgq.OpId :=
  opsWhere fun o => fixityOf o == .«infix» && takes o 2 .relation
/-- The relational unary prefixes: `~`, `^`, `*`. The label projections are
    prefixes too, but they yield a value rather than a relation. -/
private meta def relUnaries : List Sgq.OpId :=
  opsWhere fun o =>
    fixityOf o == .«prefix» && takes o 1 .relation && o.kinds.yields == some .relation
private meta def projections : List Sgq.OpId :=
  opsWhere fun o => fixityOf o == .«prefix» && takes o 1 .relation && o.kinds.yields != some .relation
private meta def connectives : List Sgq.OpId :=
  opsWhere fun o => fixityOf o == .«infix» && takes o 2 .boolean
private meta def comparisons : List Sgq.OpId :=
  (Sgq.Construct.of .«comparison»).operators.filter (Sgq.Op.of · |>.evaluates)
private meta def multTests : List Sgq.OpId :=
  (Sgq.Construct.of .«multiplicityTest»).operators.filter (Sgq.Op.of · |>.evaluates)
private meta def quantifiers : List Sgq.OpId :=
  (Sgq.Construct.of .«quantifier»).operators.filter fun o =>
    (Sgq.Op.of o).evaluates && (Sgq.Op.of o).kinds.yields == some .boolean
private meta def constants : List Sgq.OpId :=
  (Sgq.Construct.of .«constant»).operators.filter (Sgq.Op.of · |>.evaluates)
private meta def multiplicities : List String :=
  (Sgq.Construct.of .«product» |>.part .«multiplicity»).spellings

private meta def name (o : Sgq.OpId) : String := Sgq.opName o

/-! ## The corpus -/

private meta def a : Sel := .rel "a"
private meta def b : Sel := .rel "b"
private meta def c : Sel := .rel "c"

private meta def bases : List (String × Sel) :=
  [("sig", .sig `Foo "Foo"), ("rel", .rel "tr"), ("rel/", .rel "/"),
   ("relKw", .rel "in"), ("relSpace", .rel "a b"), ("relUni", .rel "σ"),
   ("relEmpty", .rel ""), ("relSlashy", .rel "util/ordering"), ("relDbl", .rel "//"),
   ("var", .var `x), ("varUni", .var `σ), ("atom", atomLit "atom_0"),
   ("raw", .raw "x or y")]

private meta def fA : Sel := unary .«nonEmpty» a
private meta def fB : Sel := unary .«empty» b
private meta def fC : Sel := unary .«exactlyOne» c

private meta def ints : List (String × Sel) :=
  [("lit", .num 7), ("litNeg", .num (-3)), ("card", unary .«cardinality» a),
   ("cardUnion", unary .«cardinality» (binary .«union» a b)),
   ("cardJoin", unary .«cardinality» (binary .«join» a b)),
   ("proj", unary .«labelNumber» a),
   ("projUnion", unary .«labelNumber» (binary .«union» a b)),
   ("add", call "add" #[.num 1, .num 2]),
   ("sub", call "subtract" #[unary .«cardinality» a, unary .«labelNumber» b]),
   ("div", call "divide" #[.num 1, .num 2]),
   ("rem", call "remainder" #[.num 1, .num 2]),
   ("abs", call "abs" #[.num 1]), ("sign", call "sign" #[.num 1]),
   ("floor", call "floor" #[.num 1]), ("ceil", call "ceil" #[.num 1]),
   ("sum", call "sum" #[unary .«labelNumber» a]),
   ("min", call "min" #[unary .«labelNumber» (binary .«union» a b)]),
   ("max", call "max" #[unary .«labelNumber» a]),
   ("sumQ", quant .«sum» false #[(`x, a)] (unary .«cardinality» (binary .«join» (.var `x) b)))]

private meta def vals : List (String × Sel) :=
  [("plain", unary .«label» a), ("str", unary .«labelString» (binary .«join» a b)),
   ("bool", unary .«labelBoolean» (binary .«union» a b)),
   ("ctor", .ctorLit `Foo.tt "tt"), ("strLit", .str "hi"),
   ("strEsc", .str "a\"b\\c\nd\te\r"), ("boolT", .boolLit true), ("boolF", .boolLit false)]

private meta def emit (label s : String) : StateM (Array (String × String)) Unit :=
  modify (·.push (label, s))

private meta def corpus : Array (String × String) :=
  StateT.run (m := Id) (do
    for (nm, s) in bases do emit s!"base.{nm}" s.toSGQ
    for k in constants do emit s!"base.{name k}" (nullary k).toSGQ
    for u in relUnaries do
      let nm := name u
      for (bn, s) in bases do emit s!"un.{nm}.{bn}" (unary u s).toSGQ
      for op in relBinaries do
        emit s!"un.{nm}.over.{name op}" (unary u (binary op a b)).toSGQ
        emit s!"un.{nm}.under.{name op}.l" (binary op (unary u a) b).toSGQ
        emit s!"un.{nm}.under.{name op}.r" (binary op a (unary u b)).toSGQ
      emit s!"un.{nm}.nest" (unary u (unary u a)).toSGQ
    for o1 in relBinaries do
      emit s!"bin.{name o1}" (binary o1 a b).toSGQ
      for o2 in relBinaries do
        emit s!"bin.{name o1}.l.{name o2}" (binary o1 (binary o2 a b) c).toSGQ
        emit s!"bin.{name o1}.r.{name o2}" (binary o1 a (binary o2 b c)).toSGQ
    for lm in "" :: multiplicities do
      for rm in "" :: multiplicities do
        let opt (s : String) := if s.isEmpty then none else some s
        emit s!"prodMult.{lm}.{rm}" (prod (opt lm) (opt rm) a b).toSGQ
    emit "prodMult.nest"
      (prod (some "one") none (binary .«union» a b) (binary .«join» b c)).toSGQ
    emit "boxJoin.one" (boxJoin a #[b]).toSGQ
    emit "boxJoin.many" (boxJoin (binary .«union» a b) #[b, c]).toSGQ
    emit "compr.one" (compr #[(`x, a)] (cmp .«subset» false (.var `x) b)).toSGQ
    emit "compr.grouped"
      (compr #[(`x, a), (`y, a), (`z, b)] (cmp .«equal» false (.var `x) (.var `z))).toSGQ
    emit "compr.quoted" (compr #[(`in, a)] (unary .«nonEmpty» (.var `in))).toSGQ
    for (nm, i) in ints do emit s!"int.{nm}" i.toSGQ
    for (nm, v) in vals do emit s!"val.{nm}" v.toSGQ
    for o in comparisons do
      emit s!"cmp.{name o}" (cmp o false a b).toSGQ
      emit s!"cmp.{name o}.neg" (cmp o true a b).toSGQ
      emit s!"cmp.{name o}.num" (cmp o false (unary .«cardinality» a) (.num 2)).toSGQ
    emit "cmp.val" (cmp .«equal» false (unary .«label» a) (.str "x")).toSGQ
    emit "cmp.valNeg" (cmp .«equal» true (unary .«labelBoolean» a) (.boolLit true)).toSGQ
    emit "cmp.rawL" (cmp .«subset» false (.raw "x or y") b).toSGQ
    emit "cmp.rawRaw" (cmp .«equal» false (.raw "x or y") (.raw "p and q")).toSGQ
    for m in multTests do emit s!"mult.{name m}" (unary m (binary .«union» a b)).toSGQ
    emit "form.not" (unary .«not» fA).toSGQ
    emit "form.notNot" (unary .«not» (unary .«not» fA)).toSGQ
    for f1 in connectives do
      let n1 := name f1
      emit s!"conn.{n1}" (binary f1 fA fB).toSGQ
      for f2 in connectives do
        emit s!"conn.{n1}.l.{name f2}" (binary f1 (binary f2 fA fB) fC).toSGQ
        emit s!"conn.{n1}.r.{name f2}" (binary f1 fA (binary f2 fB fC)).toSGQ
      emit s!"conn.{n1}.notL" (binary f1 (unary .«not» fA) fB).toSGQ
      emit s!"conn.{n1}.iteL" (binary f1 (implies fA fB (some fC)) fC).toSGQ
      emit s!"conn.{n1}.iteR" (binary f1 fA (implies fA fB (some fC))).toSGQ
      emit s!"conn.{n1}.quantL" (binary f1 (quant .«all» false #[(`x, a)] fB) fC).toSGQ
    emit "form.ite" (implies fA fB (some fC)).toSGQ
    emit "form.iteNest" (implies fA (implies fA fB (some fC)) (some fC)).toSGQ
    for q in quantifiers do
      let nm := name q
      emit s!"quant.{nm}" (quant q false #[(`x, a)] fB).toSGQ
      emit s!"quant.{nm}.disj" (quant q true #[(`x, a), (`y, a)] fB).toSGQ
      emit s!"quant.{nm}.mixed" (quant q false #[(`x, a), (`y, b), (`z, b)] fB).toSGQ
    emit "quant.nested" (quant .«all» false #[(`x, a)]
      (quant .«some» false #[(`y, b)] (cmp .«subset» false (.var `x) (.var `y)))).toSGQ
    emit "quant.underAnd" (binary .«and» (quant .«all» false #[(`x, a)] fB) fC).toSGQ
  ) #[] |>.2

/-- The pinned lowering, one `label<TAB>sgq` per line. Re-bless with
    `just rebless-sgq` after a deliberate change, then read the diff. -/
private meta def goldenPath : System.FilePath :=
  "tests" / "SelectorLoweringTest.golden.tsv"

private meta def rendered : String :=
  String.join (corpus.toList.map fun (label, sgq) => s!"{label}\t{sgq}\n")

private meta def parseGolden (s : String) : Array (String × String) :=
  (s.splitOn "\n").toArray.filterMap fun line =>
    match line.splitOn "\t" with
    | [label, sgq] => some (label, sgq)
    | _ => none

#eval show Lean.MetaM Unit from do
  -- `just rebless-sgq` sets this; the build never does, so a drifting lowering
  -- still fails there.
  if (← IO.getEnv "SPYTIAL_REBLESS").isSome then
    IO.FS.writeFile goldenPath rendered
    logInfo m!"rewrote {goldenPath}; read the diff"
    return
  let want := parseGolden (← IO.FS.readFile goldenPath)
  let got := corpus
  unless got.size == want.size do
    throwError "corpus has {got.size} cases, golden has {want.size}"
  let bad := (got.zip want).filterMap fun ((l, g), (l', w)) =>
    if l != l' then some s!"label drift: {l} vs {l'}"
    else if g != w then some s!"{l}: got {repr g}, want {repr w}"
    else none
  unless bad.isEmpty do
    throwError "SGQ lowering drifted in {bad.size} of {got.size} cases (`just \
      rebless-sgq` if the change was deliberate):\n{"\n".intercalate bad.toList}"

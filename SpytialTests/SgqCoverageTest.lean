module

public import Lean
public meta import SpytialLean.SelectorElab

open SpytialLean Lean

/-! # Coverage — what of simple-graph-query's language this package models

Operators used to be modelled one Lean constructor at a time, and this file
was the ledger that kept the account. They are not any more: the parser rules,
the elaborator and the lowering all read `Sgq.Construct.template`, so every
construct and every operator is covered by construction and an operator added
upstream needs no code.

What can still fall behind is the handful of constructs that get *no* generated
rule. Each is excluded for a reason that has nothing to do with the construct
itself — the engine refuses to run it, or Lean's own lexer claims its spelling,
or it is an atom whose spelling is an identifier and so is read off the
identifier instead. This file accounts for exactly those, and fails when a
construct upstream lands in none of them or in more than one.
-/

private meta inductive Why where
  /-- Gets a rule from `derive_sgq_rules`. -/
  | generated
  /-- The engine parses it and refuses to evaluate it. -/
  | declined (reason : String)
  /-- Its spelling is an identifier, so an atom-keyed rule would never fire on
      an unspaced `univ.lo`; `resolveIdent` reads it off the identifier. -/
  | wordAtom
  /-- Lean's lexer reads its spelling structurally before any token table sees
      it, so it has a rule written by hand. -/
  | hostLexed (rule : Name)
  deriving Inhabited

/-- Why each construct is or is not in the generated grammar. Every id in
    `Sgq.allConstructs` needs a row, so a construct added upstream fails here
    rather than passing unnoticed. -/
private meta def account : List (Sgq.ConstructId × Why) :=
  [ (.«let», .hostLexed ``sgqLetRule),
    (.«bind», .declined "Alloy's `bind`; nothing has asked for it"),
    (.«quantifier», .generated),
    (.«or», .generated), (.«xor», .generated), (.«iff», .generated),
    (.«implies», .generated), (.«and», .generated), (.«not», .generated),
    (.«comparison», .generated), (.«multiplicityTest», .generated),
    (.«unionDifference», .generated), (.«cardinality», .generated),
    (.«override», .generated), (.«intersection», .generated),
    (.«product», .generated), (.«restriction», .generated),
    (.«application», .generated), (.«join», .generated),
    (.«appliedName», .declined "a grammar corner, redundant with the box join"),
    (.«unaryPrefix», .generated),
    (.«constant», .wordAtom),
    (.«name», .wordAtom),
    (.«atName», .declined "Alloy-specific"),
    (.«atomLiteral», .hostLexed ``sgqAtomLitRule),
    (.«this», .declined "Alloy-specific"),
    (.«comprehension», .generated), (.«grouping», .generated),
    (.«block», .generated),
    (.«sexpr», .declined "reserved for the engine's internal use") ]

/-- `let` is the one construct we implement past the engine: it parses there and
    is refused, and we desugar it by substitution. It is listed as `hostLexed`
    above because that is the shape of its entry — a rule of our own — and this
    records why the reason differs. -/
private meta def implementedPastTheEngine : List Sgq.ConstructId := [.«let»]

private meta def report : Lean.Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let cats := (Lean.Parser.parserExtension.getState env).categories
  let some cat := cats.find? `spytial_sel | throwError "no category spytial_sel"
  let mut problems : Array String := #[]

  -- every construct accounted for, exactly once
  for c in Sgq.allConstructs do
    let rows := (account.filter (·.1 == c)).length
    unless rows == 1 do
      problems := problems.push
        s!"'{Sgq.constructName c}' has {rows} rows here; want exactly one"
  for (c, _) in account do
    unless Sgq.allConstructs.contains c do
      problems := problems.push s!"'{Sgq.constructName c}' is no longer in the manifest"

  for (c, why) in account do
    let cd := Sgq.Construct.of c
    let name := Sgq.constructName c
    let registered (n : Name) := cat.kinds.contains n
    match why with
    | .generated =>
      unless hasRule cd do
        problems := problems.push s!"'{name}' is claimed generated, but `hasRule` declines it"
      unless registered (ruleDeclName c) do
        problems := problems.push s!"'{name}' is claimed generated, but no rule is registered for it"
    | .declined reason =>
      if cd.evaluates then
        problems := problems.push
          s!"'{name}' is declined ({reason}), but the engine now evaluates it"
      if registered (ruleDeclName c) && !implementedPastTheEngine.contains c then
        problems := problems.push s!"'{name}' is declined, but a rule is registered for it"
    | .wordAtom =>
      if hasRule cd then
        problems := problems.push s!"'{name}' is claimed to be read off the identifier, but it has a rule"
      unless cd.fixity == .atom && cd.spellings.all (·.all Char.isAlpha) do
        problems := problems.push
          s!"'{name}' is claimed to be read off the identifier, but it is no longer a word-spelled atom"
    | .hostLexed rule =>
      if hasRule cd then
        problems := problems.push s!"'{name}' is claimed hand-written, but `hasRule` also accepts it"
      unless env.contains rule do
        problems := problems.push s!"'{name}' names {rule}, which does not exist"
      unless registered rule do
        problems := problems.push s!"'{name}' is claimed hand-written, but no rule is registered for it"

  unless problems.isEmpty do
    throwError "selector coverage is out of date ({problems.size}):\n{
      "\n".intercalate problems.toList}"
  logInfo m!"{Sgq.allConstructs.length} constructs, {Sgq.allOps.length} operators; \
    {(account.filter (·.2 matches .generated)).length} rules generated, \
    {(account.filter (·.2 matches .hostLexed _)).length} written by hand, \
    {(account.filter (·.2 matches .wordAtom)).length} read off the identifier, \
    {(account.filter (·.2 matches .declined _)).length} the engine refuses to run"

/-- info: 30 constructs, 52 operators; 21 rules generated, 2 written by hand, 2 read off the identifier, 5 the engine refuses to run -/
#guard_msgs in
run_cmd report

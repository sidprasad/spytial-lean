module

public import Lean
public meta import SpytialLean.Types
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.SelectorElab

namespace SpytialLean

open Lean Meta

public section

/-! # Values in context

In a proof you often hold a value you don't fully know — an abstract
hypothesis, a term with holes. The subject of a diagram is that *value*; the
local context is the knowledge source that decides how much of it we can
draw:

- **Opaque hole.** All the context knows is the type: one atom of that type
  (`holeAtom?` in the walker already does that).
- **The elaborator knows structure.** A `refine` assigned the metavariable, a
  `let` bound the variable to a partially built term: `instantiateMVars` and
  the let-value reveal it, and the still-open holes draw as atoms inside it.
- **The hypotheses know structure.** `h : x = t` refines `x` into `t`'s
  structure (the refinement map, consumed by `holeAtom?`).
- **The hypotheses know facts.** A Prop hypothesis mentioning the subject
  becomes tuples anchored on the subject's atoms: `h : R x y` in relation
  `R`; `h : x ≠ y` and `h : ¬ P x` in the distinguished negative relations
  (`≠`, `¬P`) — the name carries the semantics on the wire; the library
  never styles them, or anything else, by default. A conjunction splits:
  each `∧`-part draws on its own, because every part of a true conjunction
  holds. An `∨` does not split — one side holds but we do not know which —
  and a `∀` is a rule, not one fact; both are counted, not guessed. A
  negative fact draws only between values already in the world: ruling a
  term out is not license to materialize it, so `h : x ≠ node a b` against
  a term not in the diagram is counted, not drawn.

The goal is deliberately *not* drawn: hypotheses are established knowledge,
the goal is what is still being proven. -/

/-! ## Refinements: what the context says a variable is -/

/-- One refinement the context states: `var` is `rhs`. -/
meta structure Refinement where
  var : FVarId
  rhs : Expr

/-- Split nested conjunctions: `p ∧ q ∧ r` is three facts glued together
    with `∧`, and each part stands on its own — if the conjunction holds,
    every part holds. A non-conjunction is one part. -/
meta partial def conjuncts (ty : Expr) : Array Expr :=
  match ty.app2? ``And with
  | some (p, q) => conjuncts p ++ conjuncts q
  | none => #[ty]

/-- The function-graph reading of one equation side: `t.height = 3` states
    that `(t, 3)` is a point of `height`'s graph, so it can draw as a
    `height` tuple attached to `t` — not as a floating `=` between a stuck
    atom and a literal. Applies when the side applies a named function (not
    a constructor — a constructor application is a value) to at least one
    data argument. -/
private meta def graphSide? (side : Expr) : MetaM (Option (String × Array Expr)) := do
  let name? ← match side.getAppFn with
    | .const n _ =>
      match (← getEnv).find? n with
      | some (.ctorInfo _) => pure none
      | _ => pure (some (shortName n))
    | .fvar id => pure (some (hypLabel (← id.getUserName)))
    | _ => pure none
  let some name := name? | return none
  let mut args : Array Expr := #[]
  for a in side.getAppArgs do
    if ← isProofArg a then continue
    if (← Meta.isClass? (← inferType a)).isSome then continue
    args := args.push a
  if args.isEmpty then return none
  return some (name, args)

/-- The refinement one Prop states, if any: an equation with a plain
    variable on one side that does not occur in the other. An equation
    against a function application is a graph point (`a = root x` draws as
    `root[x, a]`), not a refinement into a stuck term — refining only pays
    when the other side brings structure. Shared between the harvest and the
    fact walk, so a fact that merely restates an applied refinement is
    recognized and not drawn again. -/
meta def refinementOf? (ty : Expr) : MetaM (Option (FVarId × Expr)) := do
  let some (_, lhs, rhs) := ty.eq? | return none
  let pick (id : FVarId) (other : Expr) : MetaM (Option (FVarId × Expr)) := do
    if other.containsFVar id then return none
    if (← graphSide? other).isSome then return none
    return some (id, other)
  match lhs, rhs with
  | .fvar id, _ => pick id rhs
  | _, .fvar id => pick id lhs
  | _, _ => return none

/-- The refinement candidates of one local context, in context order: `let`
    bindings (elaborator-known structure), and equations with a plain
    variable on one side — conjunctions split, so an equation inside an `∧`
    refines too. The first entry on a variable wins; later equations render
    as ordinary `=` tuples. -/
meta def equationRefinements (lctx : LocalContext) : MetaM (Array Refinement) := do
  let mut seen : Std.HashSet FVarId := {}
  let mut out : Array Refinement := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let picks : Array (FVarId × Expr) ← do
      if let some v := decl.value? then
        let v ← instantiateMVars v
        pure (if v.containsFVar decl.fvarId then #[] else #[(decl.fvarId, v)])
      else
        (conjuncts (← instantiateMVars decl.type)).filterMapM refinementOf?
    for (var, t) in picks do
      unless seen.contains var do
        seen := seen.insert var
        out := out.push { var, rhs := t }
  return out

/-! ## Prop facts as relation tuples -/

/-- Peel one negation: `¬ p` (and the definitional spelling `p → False`)
    uncovers `p`. -/
private meta def peelNot (ty : Expr) : Expr × Bool :=
  match ty with
  | .app (.const ``Not _) inner => (inner, true)
  | .forallE _ dom body _ =>
    if !body.hasLooseBVar 0 && body.isConstOf ``False then (dom, true) else (ty, false)
  | _ => (ty, false)

/-- The decomposition `walkPropTuple` performs, without walking: the relation
    name, the data arguments, and whether the Prop was negated. Shared with
    `scopeInContext` so predicted names cannot drift from emitted ones.
    `none` when the Prop does not decompose: no named head, or no data
    arguments to anchor a tuple. An equation with a function application on
    one side takes the function-graph shape (`graphSide?`). -/
meta def propTupleShape? (ty : Expr) :
    MetaM (Option (String × Array Expr × Bool)) := do
  unless ← Meta.isProp ty do return none
  let (body, negated) := peelNot ty
  if let some (_, lhs, rhs) := body.eq? then
    let graph? ← do
      match ← graphSide? lhs with
      | some (n, args) => pure (some (n, args.push rhs))
      | none =>
        match ← graphSide? rhs with
        | some (n, args) => pure (some (n, args.push lhs))
        | none => pure none
    if let some (n, args) := graph? then
      return some ((if negated then negRelName n else n), args, negated)
  let some base ← propRelName? body.getAppFn | return none
  let relName :=
    if negated then
      if base == eqRelName then neRelName else negRelName base
    else base
  -- `Ne` arrives negative through the head name, not through `peelNot`
  let negated := negated || base == neRelName
  let mut dataArgs : Array Expr := #[]
  for a in body.getAppArgs do
    if ← isProofArg a then continue
    -- `a < b` is `@LT.lt Nat instLTNat a b`: the instance is `Type`-valued and
    -- survives `isProofArg`, but it is not data
    if (← Meta.isClass? (← inferType a)).isSome then continue
    dataArgs := dataArgs.push a
  if dataArgs.isEmpty then return none
  return some (relName, dataArgs, negated)

/-- One relation tuple from a Prop that names a relation: `R a₁ … aₙ` walks
    its data arguments into the shared state and emits one tuple in relation
    `R`; a negation emits into the ruled-out relation (`≠`, `¬R`) instead —
    but only between values already in the world (variables, holes): ruling a
    term out is not license to materialize it, so a negative fact against an
    absent term is not drawn. `false` when the Prop is not drawn — it does
    not decompose (a `∀`, a conjunction, a nullary Prop), or it is such a
    withheld negative fact — and the caller counts it. With exactly one data
    argument the lone atom appears with no tuple. -/
meta def walkPropTuple (cfg : WalkConfig) (ty : Expr) :
    StateT WalkState MetaM Bool := do
  let some (relName, dataArgs, negated) ← propTupleShape? ty | return false
  if negated && !dataArgs.all (fun a => a.isFVar || a.isMVar) then
    return false
  let mut ids : Array String := #[]
  let mut types : Array String := #[]
  for a in dataArgs do
    ids := ids.push (← walkExpr cfg a)
    types := types.push (← sigOfType (← inferType a))
  if dataArgs.size == 1 then return true
  modify fun s => s.addTuple relName types { atoms := ids, types }
  return true

/-! ## The in-context walk -/

private meta def exprFVars (e : Expr) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds

private meta def mentionsAny (ty : Expr) (fvars : Array FVarId) : Bool :=
  fvars.any (ty.containsFVar ·)

/-- Draw one hypothesis's facts: conjunctions split into parts
    (`conjuncts`), and each part draws on its own — unless it merely
    restates an applied refinement (the refined structure is already the
    picture), or, with `subjectOnly`, does not mention the subject. Returns
    the number of subject-relevant parts that could not be drawn. -/
private meta def walkHypFacts (cfg : WalkConfig) (subjFVars : Array FVarId)
    (subjectOnly : Bool) (hypTy : Expr) : StateT WalkState MetaM Nat := do
  let mut skipped : Nat := 0
  for part in conjuncts hypTy do
    if subjectOnly && !mentionsAny part subjFVars then continue
    if let some (var, rhs) ← refinementOf? part then
      if let some applied := cfg.refinements[var]? then
        if applied.equal rhs then continue
    unless ← walkPropTuple cfg part do
      skipped := skipped + 1
  return skipped

/-- Walk one value together with what the local context knows about it, in
    the ambient local context (tactic callers wrap with `withMainContext`).

    The subject walks first — metavariables instantiated, refinements
    applied — then every Prop hypothesis whose type mentions the subject's
    variables contributes its facts (`walkHypFacts`): conjunctions split
    into parts, each part one relation tuple sharing the subject's atoms. A
    part that merely restates an applied refinement emits nothing: the
    refined structure *is* its rendering. Typeclass instances are skipped;
    hypotheses that do not mention the subject are not this diagram's
    business.

    Refinements already present in `cfg.refinements` are *injected* — the
    caller supplied them — and win: a context equation on the same variable
    is absorbed when it agrees (structurally), and otherwise stays an
    ordinary `=` tuple — same as a second equation on an already-refined
    variable (`equationRefinements` is first-wins).

    With `facts?`, the automatic selection is replaced: exactly the listed
    hypotheses are drawn as facts, in the listed order, whether or not they
    mention the subject. Refinements are unaffected — they are what the
    value *is*, not a fact hung on it.

    Returns the number of selected facts that were not drawn (the caller
    reports them; headless tests stay silent). -/
meta def walkInContext (cfg : WalkConfig) (subject : Expr)
    (facts? : Option (Array FVarId) := none) :
    StateT WalkState MetaM Nat := do
  let subject ← instantiateMVars subject
  let subjFVars := exprFVars subject
  -- injected refinements win; the context's candidates fill in, first-wins
  let mut map := cfg.refinements
  for e in ← equationRefinements (← getLCtx) do
    unless map.contains e.var do
      map := map.insert e.var e.rhs
  let cfg := { cfg with refinements := map }
  let _ ← walkExpr cfg subject
  let mut skipped : Nat := 0
  match facts? with
  | some facts =>
    for fvarId in facts do
      skipped := skipped +
        (← walkHypFacts cfg subjFVars false (← instantiateMVars (← fvarId.getType)))
  | none =>
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let hypTy ← instantiateMVars decl.type
      unless mentionsAny hypTy subjFVars do continue
      if (← Meta.isClass? hypTy).isSome then continue
      unless ← Meta.isProp hypTy do continue
      skipped := skipped + (← walkHypFacts cfg subjFVars true hypTy)
  return skipped

/-! ## The spec-checker vocabulary of a value in context -/

/-- The `SelScope` ops on an in-context diagram elaborate against: the
    subject type's own scope — so a spec registered with `spytial_spec` for
    the type applies unchanged — extended with one relation entry per
    decomposable Prop fact and with the fact arguments' type scopes.

    Negative names (`≠`, `¬R`) are addressable in field positions via escaped
    idents (`edgeStyle «≠» …`); they cannot occur *inside* selector
    expressions — the query language cannot lex them. Equations are predicted
    as `=` tuples even when the walk refines them away: a superset vocabulary
    is always safe. With `facts?`, the prediction covers exactly the listed
    hypotheses, mirroring `walkInContext`. -/
meta def scopeInContext (subject : Expr) (facts? : Option (Array FVarId) := none) :
    MetaM SelScope := do
  let subject ← instantiateMVars subject
  let subjFVars := exprFVars subject
  let mut scope : SelScope ← match ← typeHead? (← inferType subject) with
    | some root => SelScope.ofType root
    | none => pure { root := `_subject, lenient := true }
  -- the same selection walkInContext draws from: the listed hypotheses, or
  -- every subject-relevant Prop hypothesis
  let hypTys ← match facts? with
    | some facts => facts.mapM (fun fvarId => do instantiateMVars (← fvarId.getType))
    | none => do
      let mut tys : Array Expr := #[]
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let hypTy ← instantiateMVars decl.type
        unless mentionsAny hypTy subjFVars do continue
        if (← Meta.isClass? hypTy).isSome then continue
        tys := tys.push hypTy
      pure tys
  -- one head per walked fact argument; `none` marks an unpredictable
  -- vocabulary. propTupleShape? mirrors walkPropTuple, so names cannot drift.
  let mut heads : Array (Option Name) := #[]
  let mut propRels : Array (String × Nat) := #[]
  for hypTy in hypTys do
    -- split exactly as the walk does; facts the walk withholds (negatives
    -- against absent terms, restated refinements) are still predicted:
    -- a superset vocabulary is always safe
    for part in conjuncts hypTy do
      if let some (relName, dataArgs, _) ← propTupleShape? part then
        if dataArgs.size ≥ 2 then propRels := propRels.push (relName, dataArgs.size)
        for a in dataArgs do
          heads := heads.push (← typeHead? (← inferType a))
  for h in heads.filterMap id do
    scope := scope.merge (← SelScope.ofType h)
  for (n, a) in propRels do
    scope := { scope with rels :=
      match scope.rels.get? n with
      | some (o, some a') => if a' == a then scope.rels else scope.rels.insert n (o, none)
      | some (_, none) => scope.rels
      | none => scope.rels.insert n (scope.root, some a) }
  return { scope with lenient := scope.lenient || heads.contains none }

end

end SpytialLean

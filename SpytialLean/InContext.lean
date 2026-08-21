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
  becomes one tuple anchored on the subject's atoms: `h : R x y` in relation
  `R`; `h : x ≠ t` and `h : ¬ P x` in the distinguished negative relations
  (`≠`, `¬P`) — the name carries the semantics on the wire; the library
  never styles them, or anything else, by default.

The goal is deliberately *not* drawn: hypotheses are established knowledge,
the goal is what is still being proven. -/

/-! ## Refinements: what the context says a variable is -/

/-- One context entry usable as a refinement of `var` into `rhs`: an
    equational hypothesis `hyp : var = rhs` (or `rhs = var`), or a
    `let var := rhs` binding — in that case `hyp = var`. -/
meta structure Refinement where
  hyp : FVarId
  var : FVarId
  rhs : Expr

/-- The refinement candidates of one local context, in context order: `let`
    bindings (elaborator-known structure), and equations with a plain
    variable on one side that does not occur in the other. The first entry on
    a variable wins; later equations render as ordinary `=` tuples. -/
meta def equationRefinements (lctx : LocalContext) : MetaM (Array Refinement) := do
  let mut seen : Std.HashSet FVarId := {}
  let mut out : Array Refinement := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let pick? : Option (FVarId × Expr) ← do
      if let some v := decl.value? then
        let v ← instantiateMVars v
        pure (if v.containsFVar decl.fvarId then none else some (decl.fvarId, v))
      else
        let ty ← instantiateMVars decl.type
        pure <| match ty.eq? with
          | some (_, .fvar id, rhs) =>
            if rhs.containsFVar id then none else some (id, rhs)
          | some (_, lhs, .fvar id) =>
            if lhs.containsFVar id then none else some (id, lhs)
          | _ => none
    if let some (var, t) := pick? then
      unless seen.contains var do
        seen := seen.insert var
        out := out.push { hyp := decl.fvarId, var, rhs := t }
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
    name and the data arguments. Shared with `scopeInContext` so predicted
    names cannot drift from emitted ones. `none` when the Prop does not
    decompose: no named head, or no data arguments to anchor a tuple. -/
meta def propTupleShape? (ty : Expr) :
    MetaM (Option (String × Array Expr)) := do
  unless ← Meta.isProp ty do return none
  let (body, negated) := peelNot ty
  let some base ← propRelName? body.getAppFn | return none
  let relName :=
    if negated then
      if base == eqRelName then neRelName else negRelName base
    else base
  let mut dataArgs : Array Expr := #[]
  for a in body.getAppArgs do
    if ← isProofArg a then continue
    -- `a < b` is `@LT.lt Nat instLTNat a b`: the instance is `Type`-valued and
    -- survives `isProofArg`, but it is not data
    if (← Meta.isClass? (← inferType a)).isSome then continue
    dataArgs := dataArgs.push a
  if dataArgs.isEmpty then return none
  return some (relName, dataArgs)

/-- One relation tuple from a Prop that names a relation: `R a₁ … aₙ` walks
    its data arguments into the shared state and emits one tuple in relation
    `R`; a negation emits into the ruled-out relation (`≠`, `¬R`) instead.
    `false` when the Prop does not decompose (a `∀`, a conjunction, a nullary
    Prop) — the caller counts it as skipped. With exactly one data argument
    the lone atom appears with no tuple. -/
meta def walkPropTuple (cfg : WalkConfig) (ty : Expr) :
    StateT WalkState MetaM Bool := do
  let some (relName, dataArgs) ← propTupleShape? ty | return false
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

/-- Walk one value together with what the local context knows about it, in
    the ambient local context (tactic callers wrap with `withMainContext`).

    The subject walks first — metavariables instantiated, refinements
    applied — then every Prop hypothesis whose type mentions the subject's
    variables becomes a relation tuple (`walkPropTuple`) sharing the
    subject's atoms. A hypothesis consumed as a refinement emits nothing: the
    refined structure *is* its rendering. Typeclass instances are skipped;
    hypotheses that do not mention the subject are not this diagram's
    business.

    Refinements already present in `cfg.refinements` are *injected* — a found
    model, say — and win: a context equation on the same variable is absorbed
    when it agrees (structurally), and otherwise stays an ordinary `=` tuple —
    same as a second equation on an already-refined variable
    (`equationRefinements` is first-wins).

    Returns the number of subject-relevant Prop hypotheses that did not
    decompose (the caller reports them; headless tests stay silent). -/
meta def walkInContext (cfg : WalkConfig) (subject : Expr) :
    StateT WalkState MetaM Nat := do
  let subject ← instantiateMVars subject
  let subjFVars := exprFVars subject
  -- reconcile the context's refinements with the injected ones: injected
  -- entries win, and an entry is consumed (emits no tuple) only when it is
  -- the refinement actually applied
  let mut map := cfg.refinements
  let mut consumed : Std.HashSet FVarId := {}
  for e in ← equationRefinements (← getLCtx) do
    match map[e.var]? with
    | some prev =>
      if prev.equal e.rhs then consumed := consumed.insert e.hyp
    | none =>
      map := map.insert e.var e.rhs
      consumed := consumed.insert e.hyp
  let cfg := { cfg with refinements := map }
  let _ ← walkExpr cfg subject
  let mut skipped : Nat := 0
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if consumed.contains decl.fvarId then continue
    let hypTy ← instantiateMVars decl.type
    unless mentionsAny hypTy subjFVars do continue
    if (← Meta.isClass? hypTy).isSome then continue
    if ← Meta.isProp hypTy then
      unless ← walkPropTuple cfg hypTy do
        skipped := skipped + 1
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
    is always safe. -/
meta def scopeInContext (subject : Expr) : MetaM SelScope := do
  let subject ← instantiateMVars subject
  let subjFVars := exprFVars subject
  let mut scope : SelScope ← match ← typeHead? (← inferType subject) with
    | some root => SelScope.ofType root
    | none => pure { root := `_subject, lenient := true }
  -- one head per walked fact argument; `none` marks an unpredictable
  -- vocabulary. propTupleShape? mirrors walkPropTuple, so names cannot drift.
  let mut heads : Array (Option Name) := #[]
  let mut propRels : Array (String × Nat) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let hypTy ← instantiateMVars decl.type
    unless mentionsAny hypTy subjFVars do continue
    if (← Meta.isClass? hypTy).isSome then continue
    if let some (relName, dataArgs) ← propTupleShape? hypTy then
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

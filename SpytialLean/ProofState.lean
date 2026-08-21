module

public import Lean
public meta import SpytialLean.Types
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.SelectorElab

namespace SpytialLean

open Lean Meta

public section

/-! # Proof-state relationalization

Walks one goal — its hypotheses and its target — into one diagram, on top of
the single-value walker (`walkExpr`). One diagram is one goal: sibling goals
(the branches of a `cases`) assume contradictory things, so each gets its own
picture, never a merged one. Within the goal everything shares one walk
state, so a term appearing in a hypothesis and in the target is one atom.

There are two kinds of partially-known values here. An *opaque* hole (an
abstract hypothesis `x : T`, an unassigned metavariable `?m`) renders as one
atom of its type — `holeAtom?` in the walker already does that. A *structured*
hole is one we know more about, from two sources:

- **The elaborator.** `refine ⟨Tree.node ?l ?r, ?h⟩` assigns the witness
  metavariable; `instantiateMVars` reveals `Tree.node ?l ?r`, which the walker
  draws as real structure with the still-open holes as atoms. So this module's
  rule is: instantiate every hypothesis and goal type first, then walk.
- **The hypotheses.** `h : x = t` refines `x` into `t`'s structure (the
  refinement map, consumed by `holeAtom?`); `h : x ≠ t` and `h : ¬ P y` say
  what a value is *not*, and emit into distinguished negative relations
  (`≠`, `¬P`) that default styling draws as ruled out.

Prop hypotheses that name a relation (`h : a < b`, `h : R x y`) become one
tuple each; the goal gets the same treatment under the `⊢ ` prefix. -/

/-! ## Equational refinements -/

/-- One equational hypothesis usable as a refinement: `hyp : var = rhs` (or
    `rhs = var`) with `var` a plain variable that does not occur in `rhs`. -/
meta structure Refinement where
  hyp : FVarId
  var : FVarId
  rhs : Expr

/-- The refinement candidates of one local context, in context order. The
    first equation on a variable wins; later ones render as ordinary `=`
    tuples. -/
meta def equationRefinements (lctx : LocalContext) : MetaM (Array Refinement) := do
  let mut seen : Std.HashSet FVarId := {}
  let mut out : Array Refinement := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let some (_, lhs, rhs) := ty.eq? | continue
    let pick? : Option (FVarId × Expr) :=
      match lhs, rhs with
      | .fvar id, _ => if rhs.containsFVar id then none else some (id, rhs)
      | _, .fvar id => if lhs.containsFVar id then none else some (id, lhs)
      | _, _ => none
    if let some (var, t) := pick? then
      unless seen.contains var do
        seen := seen.insert var
        out := out.push { hyp := decl.fvarId, var, rhs := t }
  return out

/-! ## Prop applications as relation tuples -/

/-- Peel one negation: `¬ p` (and the definitional spelling `p → False`)
    uncovers `p`. -/
private meta def peelNot (ty : Expr) : Expr × Bool :=
  match ty with
  | .app (.const ``Not _) inner => (inner, true)
  | .forallE _ dom body _ =>
    if !body.hasLooseBVar 0 && body.isConstOf ``False then (dom, true) else (ty, false)
  | _ => (ty, false)

/-- The decomposition `walkPropTuple` performs, without walking: the relation
    name and the data arguments. Shared with `proofStateScope` so predicted
    names cannot drift from emitted ones. `none` when the Prop does not
    decompose: no named head, or no data arguments to anchor a tuple. -/
meta def propTupleShape? (pfx : String) (ty : Expr) :
    MetaM (Option (String × Array Expr)) := do
  unless ← Meta.isProp ty do return none
  let (body, negated) := peelNot ty
  let some base ← propRelName? body.getAppFn | return none
  let relName :=
    if negated then
      pfx ++ (if base == eqRelName then neRelName else negRelName base)
    else pfx ++ base
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
    `pfx ++ R`; a negation emits into the ruled-out relation (`≠`, `¬R`)
    instead. `false` when the Prop does not decompose (a `∀`, a conjunction,
    a nullary Prop) — the caller counts it as skipped. With exactly one data
    argument the lone atom appears with no tuple. -/
meta def walkPropTuple (cfg : WalkConfig) (pfx : String) (ty : Expr) :
    StateT WalkState MetaM Bool := do
  let some (relName, dataArgs) ← propTupleShape? pfx ty | return false
  let mut ids : Array String := #[]
  let mut types : Array String := #[]
  for a in dataArgs do
    ids := ids.push (← walkExpr cfg a)
    types := types.push (← sigOfType (← inferType a))
  if dataArgs.size == 1 then return true
  modify fun s => s.addTuple relName types { atoms := ids, types }
  return true

/-! ## The proof-state walk -/

private meta def exprFVars (e : Expr) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds

private meta def mentionsAny (ty : Expr) (fvars : Array FVarId) : Bool :=
  fvars.any (ty.containsFVar ·)

/-- Walk one goal's local context and target into the walk state. One diagram
    is one goal; within it, a term appearing in a hypothesis and in the target
    is the same atom.

    Inside the goal's own context, with every type `instantiateMVars`'d:
    a Prop hypothesis becomes a relation tuple (`walkPropTuple`); a data
    hypothesis walks through the normal walker (an abstract variable is one
    typed atom); hypotheses that are themselves types or relations
    (`isVocabularyType`) and typeclass instances are skipped; equational
    hypotheses feed the refinement map instead of emitting tuples. The goal
    target gets the tuple treatment under `goalRelPrefix`, falling back to one
    `goalAtomType` atom labeled with the pretty-printed goal.

    With a `subject?`, only the subject, the hypotheses whose types mention
    its variables, and the goal target are walked.

    Refinements already present in `cfg.refinements` are *injected* — a found
    model, say — and win: a context equation on the same variable is absorbed
    when it agrees (structurally), and otherwise stays an ordinary `=` tuple —
    same as a second equation on an already-refined variable
    (`equationRefinements` is first-wins).

    Returns the number of Prop hypotheses that did not decompose (the caller
    reports them; headless tests stay silent). -/
meta def walkProofState (cfg : WalkConfig) (goal : MVarId)
    (subject? : Option Expr := none) : StateT WalkState MetaM Nat := do
  let subjFVars := match subject? with
    | some subj => exprFVars subj
    | none => #[]
  goal.withContext do
    -- reconcile the context's equations with the injected refinements:
    -- injected entries win, and an equation is consumed (emits no tuple)
    -- only when it is the refinement actually applied
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
    let mut skipped : Nat := 0
    if let some subj := subject? then
      let _ ← walkExpr cfg subj
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let hypTy ← instantiateMVars decl.type
      if subject?.isSome && !mentionsAny hypTy subjFVars then continue
      if consumed.contains decl.fvarId then continue
      if ← Meta.isProp hypTy then
        unless ← walkPropTuple cfg "" hypTy do
          skipped := skipped + 1
      else if (← Meta.isClass? hypTy).isSome then
        continue
      else if ← isVocabularyType hypTy then
        continue
      else
        let _ ← walkExpr cfg decl.toExpr
    let goalTy ← instantiateMVars (← goal.getType)
    unless ← walkPropTuple cfg goalRelPrefix goalTy do
      let label ← ppLabel goalTy
      let s ← get
      let (atomId, s) := s.freshId
      set (s.addAtom { id := atomId, type := goalAtomType, label })
    return skipped

/-! ## The spec-checker vocabulary of a proof state -/

/-- The `SelScope` a `with [...]` block on a proof state elaborates against:
    the union of every walked hypothesis type's scope, plus one relation entry
    per decomposable Prop hypothesis and goal (exact arity from the live
    term). There is no single subject type, so the root is synthetic.

    Decorated names (`⊢ lt`, `¬R`, `≠`) are addressable in field positions via
    escaped idents (`edgeStyle «⊢ lt» …`), and the `Goal` atom type via a raw
    string selector (`atomStyle "Goal" …`); neither can occur inside selector
    expressions — the query language cannot lex them. -/
meta def proofStateScope (goal : MVarId) (subject? : Option Expr := none) :
    MetaM SelScope := do
  let subjFVars := match subject? with
    | some subj => exprFVars subj
    | none => #[]
  goal.withContext do
    -- one head per walked root; `none` marks an unpredictable vocabulary.
    -- propTupleShape? mirrors walkPropTuple, so names cannot drift.
    let mut heads : Array (Option Name) := #[]
    let mut propRels : Array (String × Nat) := #[]
    if let some subj := subject? then
      heads := heads.push (← typeHead? (← inferType subj))
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let hypTy ← instantiateMVars decl.type
      if subject?.isSome && !mentionsAny hypTy subjFVars then continue
      -- equations are predicted as `=` tuples even when the walk refines
      -- them away: a superset vocabulary is always safe
      if ← Meta.isProp hypTy then
        if let some (relName, dataArgs) ← propTupleShape? "" hypTy then
          if dataArgs.size ≥ 2 then propRels := propRels.push (relName, dataArgs.size)
          for a in dataArgs do
            heads := heads.push (← typeHead? (← inferType a))
      else if (← Meta.isClass? hypTy).isSome then
        continue
      else if ← isVocabularyType hypTy then
        continue
      else
        heads := heads.push (← typeHead? hypTy)
    let goalTy ← instantiateMVars (← goal.getType)
    if let some (relName, dataArgs) ← propTupleShape? goalRelPrefix goalTy then
      if dataArgs.size ≥ 2 then propRels := propRels.push (relName, dataArgs.size)
      for a in dataArgs do
        heads := heads.push (← typeHead? (← inferType a))
    let mut scope : SelScope := { root := `_proofState }
    scope := { scope with rels := scope.rels.insert "scrutinee" (`_proofState, some 3) }
    for h in heads.filterMap id do
      scope := scope.merge (← SelScope.ofType h)
    for (n, a) in propRels do
      scope := { scope with rels :=
        match scope.rels.get? n with
        | some (o, some a') => if a' == a then scope.rels else scope.rels.insert n (o, none)
        | some (_, none) => scope.rels
        | none => scope.rels.insert n (`_proofState, some a) }
    return { scope with lenient := scope.lenient || heads.contains none }

end

end SpytialLean

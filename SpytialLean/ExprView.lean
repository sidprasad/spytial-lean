module

public import Lean
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Spec
public meta import SpytialLean.Selector
public meta import SpytialLean.Widget
public meta import SpytialLean.Attr
public meta import SpytialLean.Command

namespace SpytialLean

open Lean Meta Elab

/-! # A `Lean.Expr` drawn as syntax

The picture a tactic author needs is the term as written: app spines as
argument fans, variables linked to their binders, implicit and instance
arguments collapsed, metavariables flagged. A custom relationalizer emits
that picture, and `ExprShape` declares its vocabulary so specs over `Expr`
are checked against it. -/

public meta register_option spytial.expr.full : Bool := {
  defValue := false
  descr := "draw every argument of an application at its position, and put \
            de Bruijn indices on variables"
}

/-- What the view emits. Never instantiated: each constructor is an atom
    type, each field a relation. `args` is the ternary index table. -/
public meta inductive ExprShape where
  | Binder (type body value : ExprShape)
  | Var (binder : ExprShape)
  | App (fn : ExprShape) (args : Nat → ExprShape) («implicit» : ExprShape)
  | Implicit
  | Const
  | Lit
  | Sort
  | MVar
  | Loose
  | MData (inner : ExprShape)
  | Proj (of : ExprShape)
  | Opaque

/-- Binder names as a reader expects them: macro scopes erased, anonymous as `_`. -/
private meta def cleanName (n : Name) : String :=
  let n := n.eraseMacroScopes
  if n.isAnonymous then "_" else toString n

private meta def sortLabel : Level → String
  | .zero => "Prop"
  | .succ .zero => "Type"
  | .succ (.succ .zero) => "Type 1"
  | _ => "Sort"

private meta def litLabel : Literal → String
  | .natVal n => toString n
  | .strVal s => s!"\"{s}\""

private meta def headLabel : Expr → String
  | .const n _ => toString n
  | .bvar i => s!"#{i}"
  | .fvar _ => "fvar"
  | .mvar _ => "?_"
  | .sort u => sortLabel u
  | .lit l => litLabel l
  | .lam .. => "fun"
  | .forallE .. => "∀"
  | .letE .. => "let"
  | .mdata _ e => headLabel e
  | .proj s i _ => s!"{s}.{i}"
  | .app .. => "app"

/-- Binder infos of `fn`'s first `args.size` parameters; `#[]` when the type
    cannot be consulted, and then every argument reads as explicit. -/
private meta def argBinderInfos (fn : Expr) (args : Array Expr) :
    MetaM (Array BinderInfo) := do
  if fn.hasLooseBVars then return #[]
  try
    let mut ty ← instantiateMVars (← inferType fn)
    let mut out : Array BinderInfo := #[]
    for a in args do
      ty ← whnf ty
      match ty with
      | .forallE _ _ body bi =>
        out := out.push bi
        ty := body.instantiate1 a
      | _ => break
    return out
  catch _ => return #[]

/-- Atom ids of the enclosing binders, innermost first, with their names. -/
private meta abbrev BinderCtx := List (String × Name)

/-- One atom per syntactic node, emitted into the walk. -/
private meta partial def emit (full : Bool) (ctx : BinderCtx) :
    Expr → StateT WalkState MetaM String
  | .bvar i => do
    match ctx[i]? with
    | some (binderId, n) =>
      let a ← emitAtom "Var" (if full then s!"{cleanName n} #{i}" else cleanName n)
      emitTuple "binder" #[a, binderId]
      return a
    | none => emitAtom "Loose" s!"#{i} loose"
  | .fvar id => do
    let n ← try id.getUserName catch _ => pure id.name
    emitAtom "Var" (cleanName n)
  | .mvar id => do
    let assigned ← id.isAssigned
    let delayed ← id.isDelayedAssigned
    let n ← try pure (← id.getDecl).userName catch _ => pure .anonymous
    let base := if n.isAnonymous then "?m" else s!"?{n}"
    emitAtom "MVar" (if assigned || delayed then s!"{base} (assigned)" else base)
  | .sort u => emitAtom "Sort" (sortLabel u)
  | .const n _ => emitAtom "Const" (toString n)
  | .lit l => emitAtom "Lit" (litLabel l)
  | .mdata kv e => do
    let keys := kv.entries.map (toString ·.1)
    let a ← emitAtom "MData" (if keys.isEmpty then "mdata" else s!"mdata {" ".intercalate keys}")
    emitTuple "inner" #[a, ← emit full ctx e]
    return a
  | .proj s i e => do
    let a ← emitAtom "Proj" s!"{s}.{i}"
    emitTuple "of" #[a, ← emit full ctx e]
    return a
  | .lam n t body _ => do
    let a ← emitAtom "Binder" s!"fun {cleanName n}"
    emitTuple "type" #[a, ← emit full ctx t]
    emitTuple "body" #[a, ← emit full ((a, n) :: ctx) body]
    return a
  | .forallE n t body _ => do
    let a ← emitAtom "Binder" (if body.hasLooseBVar 0 then s!"∀ {cleanName n}" else "→")
    emitTuple "type" #[a, ← emit full ctx t]
    emitTuple "body" #[a, ← emit full ((a, n) :: ctx) body]
    return a
  | .letE n t v body _ => do
    let a ← emitAtom "Binder" s!"let {cleanName n}"
    emitTuple "type" #[a, ← emit full ctx t]
    emitTuple "value" #[a, ← emit full ctx v]
    emitTuple "body" #[a, ← emit full ((a, n) :: ctx) body]
    return a
  | e@(.app ..) => do
    let fn := e.getAppFn
    let args := e.getAppArgs
    let a ← emitAtom "App" "app"
    emitTuple "fn" #[a, ← emit full ctx fn]
    let infos ← argBinderInfos fn args
    let mut j := 0
    for i in [0:args.size] do
      let arg := args[i]!
      if full || (infos[i]?.getD .default) == .default then
        let idx ← emitAtom "Nat" (toString (if full then i else j))
        emitTuple "args" #[a, idx, ← emit full ctx arg]
        j := j + 1
      else
        emitTuple "implicit" #[a, ← emitAtom "Implicit" (headLabel arg.getAppFn)]
    return a

private meta unsafe def recoverExprUnsafe (e : Expr) : MetaM (Option Expr) := do
  try return some (← Meta.evalExpr Expr (mkConst ``Lean.Expr) e)
  catch _ => return none

/-- The `Expr` value a walked term denotes, by evaluation. `none` for open or
    stuck terms. -/
@[implemented_by recoverExprUnsafe]
private meta opaque recoverExpr? (e : Expr) : MetaM (Option Expr)

/-- The relationalizer for `Expr`-typed values. A term whose value cannot be
    recovered, or that reaches a valueless constant, is one `Opaque` atom. -/
public meta def exprView : CustomRelationalizer := fun e _ => do
  let full := spytial.expr.full.get (← getOptions)
  if ← hasValuelessConst e then return ← emitAtom "Opaque" (← ppLabel (← whnf e))
  match ← recoverExpr? e with
  | some v => emit full [] v
  | none => emitAtom "Opaque" (← ppLabel (← whnf e))

spytial_relationalizer Lean.Expr exprView emits ExprShape

/-! ## The spec

Attached to `Lean.Expr` and checked against `ExprShape`. -/

spytial_spec Lean.Expr [
  edgeStyle «implicit» (lineStyle "#aaaaaa" dashed) noLabels,
  edgeStyle binder (lineStyle "#2f6fba" dotted),
  atomStyle Implicit (fillStyle "#eeeeee"),
  atomStyle MVar (fillStyle "#ffd166"),
  atomStyle Loose (fillStyle "#ff6b6b"),
  atomStyle Binder (fillStyle "#cfe3ff"),
  atomStyle MData (fillStyle "#e6d5f2"),
  -- the argument index draws as the edge's `args[i]` label; the index atom
  -- itself is clutter, unless it is also an endpoint
  hideAtom {x : univ |
    let source = (args) . univ . univ,
        label  = univ . (args) . univ,
        target = univ . (univ . (args))
    | x in label && x !in source && x !in target}
]

/-! ## Entries -/

/-- The type or relation whose presence in the datum justifies an op. The
    `hideAtom` arm is this spec's own knowledge: its one hide is the `args`
    index column. -/
private meta def opGate? (op : SpytialOp) : Option (String ⊕ String) :=
  match op.item with
  | .atomStyle =>
    match op.field? .selector with
    | some (.sel (.sig _ s)) => some (.inl s)
    | _ => none
  | .edgeStyle =>
    match op.field? .field with
    | some (.rel f) => some (.inr f)
    | _ => none
  | .hideAtom => some (.inr "args")
  | _ => none

/-- The widget props for `e`'s syntax tree, for the goal tactic and
    out-of-tree tooling: the datum plus the attached spec gated to what the
    datum contains, so no op chips as matched-nothing. Build the props in the
    same `MetavarContext` as the meta program that made `e`, or metavar
    assignment reads false. -/
public meta def exprViewProps (e : Expr) : MetaM Json := do
  let full := spytial.expr.full.get (← getOptions)
  let (_, st) ← (emit full [] e).run {}
  let di := st.toDataInstance
  let spec := ((getSpytialSpec? (← getEnv) ``Lean.Expr).getD []).filter fun op =>
    match opGate? op with
    | some (.inl ty) => di.atoms.any (·.type == ty)
    | some (.inr rel) => di.relations.any fun r => r.name == rel && !r.tuples.isEmpty
    | none => true
  return Json.mkObj
    [ ("dataInstance", Lean.toJson di),
      ("cndSpec", .str (← Lean.ofExcept (SpytialSpec.render spec))) ]

public section

/-- Leading parser: `spytial.goal` lexes as one qualified identifier, so the
    rule matches it by value off the ident bucket (see `spytialProofKw`). -/
meta def spytialGoalKw : Lean.Parser.Parser :=
  Lean.Parser.nonReservedSymbol "spytial.goal" (includeIdent := true)

/-- `spytial.goal` draws the goal's syntax tree mid-proof. -/
syntax (name := spytialGoalTactic) spytialGoalKw : tactic

open Tactic in
@[tactic spytialGoalTactic]
meta def elabSpytialGoalTactic : Tactic := fun stx => do
  let props ← exprViewProps (← getMainTarget)
  Widget.savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

end

end SpytialLean

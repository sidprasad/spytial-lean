module

public import Lean
public meta import SpytialLean.Display
public meta import SpytialLean.Relationalizer
public meta import SpytialLean.TypeShape
public meta import SpytialLean.Spec
public meta import SpytialLean.Selector
public meta import SpytialLean.Widget
public meta import SpytialLean.Attr
public meta import SpytialLean.Command

namespace SpytialLean

open Lean Meta Elab

/-! # Expr syntax trees through the walker

An `Expr` is syntax: the interesting picture is the term as written — spines
flattened to argument fans, binder back-edges, implicits collapsed, metavars
flagged — not the constructor cells the generic walk would draw. The view is
an ordinary inductive (`ExprViewNode`) built by an ordinary function; a
`spytial_view` registration rewrites each walked `Expr` to its view value and
the walker draws that, so identity, holes, specs and the selector vocabulary
all apply to the view with no hand emission anywhere.

`#spytial (e : Expr)` therefore renders the view. The value is recovered from
the walked term by evaluation (the walker's own idiom for identity keys and
`Repr` labels); a stuck or open term falls back to one `Opaque` leaf. -/

public meta structure ExprViewConfig where
  /-- Show every argument at its true position instead of collapsing
      implicit/instance args to stubs. Also puts de Bruijn indices on vars. -/
  full : Bool := false

/-! ## The view type

One constructor per node role. `SpytialCtorTypes` makes the constructor the
atom type, so the spec targets `Binder`, `Implicit`, `MVar`, … directly;
field binder names are the relation names. Node identity is the hidden
`(nonce, i)` id — position is the meaning — and a `Ref` carrying a binder's
id *is* that binder's atom: the back-edge is an identity merge, not a special
edge kind. -/

public meta inductive ExprViewNode where
  /-- `fun`/`∀`/`let`/`→`; `value` is the let-binding when there is one. -/
  | Binder (id : Hidden (Nat × Nat)) (text : Hidden String)
      (type : ExprViewNode) (value : Rel ExprViewNode) (body : ExprViewNode)
  /-- A variable occurrence; `binder` points back to its `Binder` (empty for
      a hypothesis). -/
  | Var (id : Hidden (Nat × Nat)) (text : Hidden String) (binder : Rel ExprViewNode)
  /-- Another node's atom, by id — always merged away by identity. -/
  | Ref (id : Hidden (Nat × Nat))
  | App (id : Hidden (Nat × Nat)) (text : Hidden String) (fn : ExprViewNode)
      (args : Rel (Nat × ExprViewNode)) («implicit» : Rel ExprViewNode)
  /-- A collapsed implicit/instance argument, labeled by its head. -/
  | Implicit (id : Hidden (Nat × Nat)) (text : Hidden String)
  | Const (id : Hidden (Nat × Nat)) (text : Hidden String)
  | Lit (id : Hidden (Nat × Nat)) (text : Hidden String)
  | Sort (id : Hidden (Nat × Nat)) (text : Hidden String)
  | MVar (id : Hidden (Nat × Nat)) (text : Hidden String)
  /-- A loose bvar — an ill-scoped index, drawn loud. -/
  | Loose (id : Hidden (Nat × Nat)) (text : Hidden String)
  | MData (id : Hidden (Nat × Nat)) (text : Hidden String) (inner : ExprViewNode)
  | Proj (id : Hidden (Nat × Nat)) (text : Hidden String) (of : ExprViewNode)
  /-- The fallback for a term whose `Expr` value cannot be recovered. -/
  | Opaque (id : Hidden (Nat × Nat)) (text : Hidden String)
  deriving ToExpr

public meta def ExprViewNode.ident : ExprViewNode → Nat × Nat
  | .Binder i .. | .Var i .. | .Ref i | .App i .. | .Implicit i .. | .Const i ..
  | .Lit i .. | .Sort i .. | .MVar i .. | .Loose i .. | .MData i .. | .Proj i ..
  | .Opaque i .. => i.val

public meta def ExprViewNode.text : ExprViewNode → String
  | .Ref _ => "‹ref›"
  | .Binder _ t .. | .Var _ t .. | .App _ t .. | .Implicit _ t .. | .Const _ t ..
  | .Lit _ t .. | .Sort _ t .. | .MVar _ t .. | .Loose _ t .. | .MData _ t ..
  | .Proj _ t .. | .Opaque _ t .. => t.val

public meta instance : SpytialCtorTypes ExprViewNode := ⟨⟩

public meta instance : SpytialDisplay ExprViewNode := ⟨ExprViewNode.text⟩

public meta instance : SpytialIdentity ExprViewNode :=
  ⟨.identity fun v => ToIdentityKey.toKey v.ident, none⟩

/-! ## Building the view -/

/-- Binder names as a reader expects them: hygiene junk (`a._@._hyg…`)
    stripped, anonymous as `_`. -/
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

/-- Binder infos of `fn`'s first `args.size` parameters. `#[]` when the type
    cannot be consulted (open `fn`, failed inference); callers then treat every
    argument as explicit rather than guessing. -/
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

private meta structure BuildCtx where
  /-- The dispatch nonce: the first id component, so nodes of different
      invocations never share an identity. -/
  nonce : Nat
  full : Bool := false

/-- Atom ids of the enclosing binders, innermost first, with their names. -/
private meta abbrev ViewCtx := List ((Nat × Nat) × Name)

private meta def fid (bc : BuildCtx) : StateT Nat MetaM (Hidden (Nat × Nat)) := do
  let i ← get
  set (i + 1)
  return ⟨(bc.nonce, i)⟩

/-- The view builder: one node per syntactic node, app spines flattened to
    `fn` plus an indexed `args` fan, implicit and instance arguments collapsed
    to `Implicit` stubs, `bvar`s wired back to their binder by `Ref`. -/
private meta partial def build (bc : BuildCtx) (ctx : ViewCtx) :
    Expr → StateT Nat MetaM ExprViewNode
  | .bvar i => do
    match ctx[i]? with
    | some (bid, n) =>
      return .Var (← fid bc)
        ⟨if bc.full then s!"{cleanName n} #{i}" else cleanName n⟩ ⟨[.Ref ⟨bid⟩]⟩
    | none => return .Loose (← fid bc) ⟨s!"#{i} loose"⟩
  | .fvar id => do
    let n ← try id.getUserName catch _ => pure id.name
    return .Var (← fid bc) ⟨cleanName n⟩ ⟨[]⟩
  | .mvar id => do
    let assigned ← id.isAssigned
    let delayed ← id.isDelayedAssigned
    let n ← try pure (← id.getDecl).userName catch _ => pure .anonymous
    let base := if n.isAnonymous then "?m" else s!"?{n}"
    return .MVar (← fid bc) ⟨if assigned || delayed then s!"{base} (assigned)" else base⟩
  | .sort u => return .Sort (← fid bc) ⟨sortLabel u⟩
  | .const n _ => return .Const (← fid bc) ⟨toString n⟩
  | .lit l => return .Lit (← fid bc) ⟨litLabel l⟩
  | .mdata kv e => do
    let keys := kv.entries.map (toString ·.1)
    let a ← fid bc
    return .MData a
      ⟨if keys.isEmpty then "mdata" else s!"mdata {" ".intercalate keys}"⟩
      (← build bc ctx e)
  | .proj s i e => do
    let a ← fid bc
    return .Proj a ⟨s!"{s}.{i}"⟩ (← build bc ctx e)
  | .lam n t body _ => do
    let a ← fid bc
    return .Binder a ⟨s!"fun {cleanName n}"⟩ (← build bc ctx t) ⟨[]⟩
      (← build bc ((a.val, n) :: ctx) body)
  | .forallE n t body _ => do
    let a ← fid bc
    return .Binder a ⟨if body.hasLooseBVar 0 then s!"∀ {cleanName n}" else "→"⟩
      (← build bc ctx t) ⟨[]⟩ (← build bc ((a.val, n) :: ctx) body)
  | .letE n t v body _ => do
    let a ← fid bc
    return .Binder a ⟨s!"let {cleanName n}"⟩ (← build bc ctx t)
      ⟨[← build bc ctx v]⟩ (← build bc ((a.val, n) :: ctx) body)
  | e@(.app ..) => do
    let fn := e.getAppFn
    let args := e.getAppArgs
    let a ← fid bc
    let fnV ← build bc ctx fn
    let infos ← argBinderInfos fn args
    let mut argVs : Array (Nat × ExprViewNode) := #[]
    let mut stubs : Array ExprViewNode := #[]
    let mut j := 0
    for i in [0:args.size] do
      let arg := args[i]!
      if bc.full then
        argVs := argVs.push (i, ← build bc ctx arg)
      else if (infos[i]?.getD .default) == .default then
        argVs := argVs.push (j, ← build bc ctx arg)
        j := j + 1
      else
        stubs := stubs.push (.Implicit (← fid bc) ⟨headLabel arg.getAppFn⟩)
    return .App a ⟨"app"⟩ fnV ⟨argVs.toList⟩ ⟨stubs.toList⟩

/-! ## The view registration -/

private meta unsafe def recoverExprUnsafe (e : Expr) : MetaM (Option Expr) := do
  try return some (← Meta.evalExpr Expr (mkConst ``Lean.Expr) e)
  catch _ => return none

/-- The `Expr` value the walked term denotes, by evaluation — the walker's own
    idiom for identity keys and `Repr` labels. `none` for open or stuck terms. -/
@[implemented_by recoverExprUnsafe]
private meta opaque recoverExpr? (e : Expr) : MetaM (Option Expr)

/-- The view value for a walked `Expr`-denoting term, as a reified term.
    Total: an unrecoverable term — open, stuck, or reaching a valueless
    constant whose evaluation would fabricate the `Inhabited` default —
    becomes one `Opaque` leaf, so the constructor cells of `Expr` itself are
    never drawn. -/
private meta def viewTermOf (cfg : ExprViewConfig) (nonce : Nat) (e : Expr) :
    MetaM (Option Expr) := do
  let opaqueLeaf : MetaM (Option Expr) := do
    return some (toExpr (ExprViewNode.Opaque ⟨(nonce, 0)⟩ ⟨← ppLabel (← Meta.whnf e)⟩))
  if ← hasValuelessConst e then return ← opaqueLeaf
  match ← recoverExpr? e with
  | some v =>
    return some (toExpr (← (build { nonce, full := cfg.full } [] v).run' 0))
  | none => opaqueLeaf

public meta def exprView : SpytialView := fun e nonce => viewTermOf {} nonce e

spytial_view Lean.Expr ExprViewNode exprView

/-! ## The spec

Attached to `Lean.Expr` — the walked type — and elaborated against the view's
vocabulary, which the selector scope reaches through the registration. -/

spytial_spec Lean.Expr [
  edgeStyle «implicit» (lineStyle "#aaaaaa" dashed) noLabels,
  edgeStyle binder (lineStyle "#2f6fba" dotted),
  atomStyle Implicit (fillStyle "#eeeeee"),
  atomStyle MVar (fillStyle "#ffd166"),
  atomStyle Loose (fillStyle "#ff6b6b"),
  atomStyle Binder (fillStyle "#cfe3ff"),
  atomStyle MData (fillStyle "#e6d5f2"),
  -- the argument index draws as the edge's `args[i]` label; the index atom
  -- itself is clutter. Endpoint subtraction, not a bare middle-column hide:
  -- an atom that is also an endpoint must survive.
  hideAtom {x : univ |
    let source = (args) . univ . univ,
        label  = univ . (args) . univ,
        target = univ . (univ . (args))
    | x in label && x !in source && x !in target}
]

/-! ## Entries -/

/-- The type or relation whose presence in the datum justifies an op — for
    gating a spec to what a particular term contains. The `hideAtom` arm is
    this spec's own knowledge: its one hide is the `args` index column. -/
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
    out-of-tree frontends: the datum plus the attached spec gated to what the
    datum contains, so no op chips as matched-nothing. `e` here is the `Expr`
    *value* (the walker's registration recovers values from walked terms
    itself). Build the props in the same `MetavarContext` as the meta program
    that made `e`, or metavar assignment reads false. -/
public meta def exprViewProps (e : Expr) (cfg : ExprViewConfig := {}) : MetaM Json := do
  let node ← (build { nonce := 0, full := cfg.full } [] e).run' 0
  let di ← relationalize (toExpr node)
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

/-- `spytial.goal` renders the goal's syntax tree mid-proof. -/
syntax (name := spytialGoalTactic) spytialGoalKw : tactic

open Tactic in
@[tactic spytialGoalTactic]
meta def elabSpytialGoalTactic : Tactic := fun stx => do
  let props ← exprViewProps (← getMainTarget)
  Widget.savePanelWidgetInfo SpytialWidget.javascriptHash (return props) stx

end

end SpytialLean

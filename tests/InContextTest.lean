module

meta import SpytialLean.InContext
meta import WalkCanon

open SpytialLean Lean Meta

/-!
# IYKYK consumer tests

These tests exercise the boundary owned by Spytial: IYKYK extracts the
knowledge, then `relationalizeAfaik` chooses atoms, labels, and relation
tuples. The extraction engine and its certification are tested in IYKYK.
-/

private meta def viewOf (label : String) (root : Expr) (config : Iykyk.Config := {})
    (observations : Array Expr := #[]) : MetaM ContextView := do
  let (status, view?) ← wdykInContext root {} config observations
  if status.inconsistent then throwError "{label}: unexpectedly inconsistent"
  let some view := view? | throwError "{label}: no context view"
  return view

/-! ## Positive and connected facts -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[x, y]) fun _ => do
    let view ← viewOf "consumer.lt" x
    assertCanon "consumer.lt" view.data "Nat|x\nNat|y\nlt[Nat,Nat]:0,1"

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun α => do
  withLocalDeclD `R (← mkArrow α (← mkArrow α (mkSort Level.zero))) fun R => do
  withLocalDeclD `S (← mkArrow α (← mkArrow α (mkSort Level.zero))) fun S => do
  withLocalDeclD `x α fun x => do
  withLocalDeclD `y α fun y => do
  withLocalDeclD `z α fun z => do
  withLocalDeclD `h₁ (mkApp2 R x y) fun _ => do
  withLocalDeclD `h₂ (mkApp2 S y z) fun _ => do
    let view ← viewOf "consumer.connected" x
    assertCanon "consumer.connected" view.data
      "α|x\nα|y\nα|z\nR[α,α]:0,1\nS[α,α]:1,2"

/-! ## Equalities refine structure -/

private inductive Tree where
  | leaf (value : Nat)
  | node (left right : Tree)

private meta def tree : Expr := mkConst ``Tree

private meta def leaf (value : Nat) : Expr :=
  mkApp (mkConst ``Tree.leaf) (mkRawNatLit value)

private meta def node (left right : Expr) : Expr :=
  mkApp2 (mkConst ``Tree.node) left right

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `t tree fun t => do
  withLocalDeclD `shape (← mkAppM ``Eq #[t, node (leaf 1) (leaf 2)]) fun _ => do
    let view ← viewOf "consumer.refinement" t
    assertCanon "consumer.refinement" view.data
      "Tree|node\nTree|leaf\nNat|1\nTree|leaf\nNat|2\n\
       left[Tree,Tree]:0,1\nright[Tree,Tree]:0,3\nvalue[Tree,Nat]:1,2;3,4"

/-! ## Existential identity survives translation -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun α => do
  withLocalDeclD `edge (← mkArrow α (← mkArrow α (mkSort Level.zero))) fun edge => do
  withLocalDeclD `source α fun source => do
  withLocalDeclD `target α fun target => do
    let routeType ← withLocalDeclD `middle α fun middle => do
      let body ← mkAppM ``And #[mkApp2 edge source middle, mkApp2 edge middle target]
      mkAppM ``Exists #[← mkLambdaFVars #[middle] body]
    withLocalDeclD `route routeType fun _ => do
      let view ← viewOf "consumer.witness" source
      assertCanon "consumer.witness" view.data
        "α|•₁\nα|source\nα|target\nedge[α,α]:1,0;0,2"

/-! ## Explicit IYKYK rules add derived relations -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun α => do
  withLocalDeclD `R (← mkArrow α (← mkArrow α (mkSort Level.zero))) fun R => do
  withLocalDeclD `S (← mkArrow α (← mkArrow α (mkSort Level.zero))) fun S => do
  withLocalDeclD `x α fun x => do
  withLocalDeclD `y α fun y => do
  withLocalDeclD `known (mkApp2 R x y) fun _ => do
    let ruleType ← withLocalDeclD `a α fun a => do
      withLocalDeclD `b α fun b => do
        mkForallFVars #[a, b] (← mkArrow (mkApp2 R a b) (mkApp2 S a b))
    withLocalDeclD `rule ruleType fun rule => do
      let view ← viewOf "consumer.rule" x { hypotheses := #[rule] }
      assertCanon "consumer.rule" view.data
        "α|x\nα|y\nR[α,α]:0,1\nS[α,α]:0,1"

/-! ## Missing knowledge remains absent -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `choice (← mkAppM ``Or #[← mkAppM ``Eq #[x, mkRawNatLit 1],
      ← mkAppM ``Eq #[x, mkRawNatLit 2]]) fun _ => do
    let view ← viewOf "consumer.disjunction" x
    assertCanon "consumer.disjunction" view.data "Nat|x"

/-! ## Symbolic applications become graph points -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun α => do
  withLocalDeclD `Reach (← mkArrow α (mkSort Level.zero)) fun Reach => do
  withLocalDeclD `next (← mkArrow α α) fun next => do
  withLocalDeclD `start α fun start => do
    let nextStart := mkApp next start
    withLocalDeclD `h₀ (mkApp Reach start) fun _ => do
    withLocalDeclD `h₁ (mkApp Reach nextStart) fun _ => do
      let view ← viewOf "consumer.functionGraph" start
      assertCanon "consumer.functionGraph" view.data
        "α|start\nα|•₁\nReach[α]:0;1\nnext[α,α]:0,1"

/-! ## Requested observations become graph points -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `measure (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) fun measure => do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let view ← viewOf "consumer.observation" x {} #[mkApp measure x]
    assertCanon "consumer.observation" view.data
      "Nat|x\nNat|•₁\nmeasure[Nat,Nat]:0,1"

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `measure (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) fun measure => do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `known (← mkAppM ``Eq #[mkApp measure x, mkRawNatLit 3]) fun _ => do
    let view ← viewOf "consumer.knownObservation" x {} #[mkApp measure x]
    assertCanon "consumer.knownObservation" view.data
      "Nat|x\nNat|3\nmeasure[Nat,Nat]:0,1"

private def Tree.height : Tree → Nat
  | .leaf _ => 0
  | .node left right => 1 + max (height left) (height right)

/- Observations parameterize fact relationalization. The source computation
    containing `height` remains `height`/`add`/`lt`; WHNF must not expose
    the implementation-level `Nat.succ` constructor and its `n` field. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `left tree fun left => do
  withLocalDeclD `right tree fun right => do
    let leftHeight := mkApp (mkConst ``Tree.height) left
    let rightHeight := mkApp (mkConst ``Tree.height) right
    let oneMore ← mkAppM ``HAdd.hAdd #[rightHeight, mkRawNatLit 1]
    withLocalDeclD `branch (← mkAppM ``LT.lt #[oneMore, leftHeight]) fun _ => do
      let view ← viewOf "consumer.observationContext" left {} #[leftHeight]
      assertCanon "consumer.observationContext" view.data
        "Tree|left\nNat|•₁\nNat|•₂\nTree|right\nNat|1\nNat|•₃\n\
         add[Nat,Nat,Nat]:2,4,1\nheight[Tree,Nat]:3,2;0,5\nlt[Nat,Nat]:1,5"
      assertMatchesReference "consumer.observationContext.reference" oneMore
        { functionGraphs := true, observations := #[leftHeight] }
      let scope ← scopeForAfaik view.afaik (← SelScope.ofType ``Tree) #[leftHeight]
      unless (scope.rels.get? "add").map (·.2) == some (some 3) do
        throwError "consumer.observationContext: expected ternary add"

/-! ## IYKYK inconsistency prevents a diagram -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `bad (mkConst ``False) fun _ => do
    let (status, view?) ← wdykInContext x
    unless status.inconsistent do throwError "consumer.false: inconsistency was not reported"
    if view?.isSome then throwError "consumer.false: inconsistent knowledge produced a view"

/-! ## Layout scope follows emitted relations -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[x, y]) fun _ => do
    let view ← viewOf "consumer.scope" x
    let scope ← scopeForAfaik view.afaik (← SelScope.ofType ``Nat)
    unless (scope.rels.get? "lt").map (·.2) == some (some 2) do
      throwError "consumer.scope: expected binary lt"

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

/- A fact whose endpoint is a constructor subterm reuses the atom reached by
   the root walk instead of drawing the entire subtree a second time. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `P (← mkArrow tree (mkSort Level.zero)) fun P => do
    let child := node (leaf 1) (leaf 2)
    let root := node child (leaf 3)
    withLocalDeclD `h (mkApp P child) fun _ => do
      let view ← viewOf "consumer.sharedSubtermFact" root { rootOnly := false }
      assertCanon "consumer.sharedSubtermFact" view.data
        "Tree|node\nTree|node\nTree|leaf\nNat|1\nTree|leaf\nNat|2\nTree|leaf\nNat|3\n\
         P[Tree]:1\nleft[Tree,Tree]:1,2;0,1\nright[Tree,Tree]:1,4;0,6\n\
         value[Tree,Nat]:2,3;4,5;6,7"

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
        "α|?₁\nα|source\nα|target\nedge[α,α]:1,0;0,2"

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
        "α|start\nα|?₁\nReach[α]:0;1\nnext[α,α]:0,1"

/-! ## Requested observations become graph points -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `measure (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) fun measure => do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let view ← viewOf "consumer.observation" x {} #[mkApp measure x]
    assertCanon "consumer.observation" view.data
      "Nat|x\nNat|?₁\nmeasure[Nat,Nat]:0,1"

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `measure (← mkArrow (mkConst ``Nat) (mkConst ``Nat)) fun measure => do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `known (← mkAppM ``Eq #[mkApp measure x, mkRawNatLit 3]) fun _ => do
    let view ← viewOf "consumer.knownObservation" x {} #[mkApp measure x]
    assertCanon "consumer.knownObservation" view.data
      "Nat|x\nNat|3\nNat|?₁\nmeasure[Nat,Nat]:0,1;1,2"

private def Tree.height : Tree → Nat
  | .leaf _ => 0
  | .node left right => 1 + max (height left) (height right)

/- An observer is lifted over the represented domain. Selecting a parent
   therefore observes the parent and both symbolic child trees. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `left tree fun left => do
  withLocalDeclD `right tree fun right => do
    let root := node left right
    let observation := mkApp (mkConst ``Tree.height) root
    assertCanon "consumer.activeDomainObservation"
      (← relationalize root {} #[observation])
      "Tree|node\nTree|left\nTree|right\nNat|?₁\nNat|?₂\nNat|?₃\n\
       height[Tree,Nat]:0,3;1,4;2,5\nleft[Tree,Tree]:0,1\nright[Tree,Tree]:0,2"

/- Values introduced by proof-backed context facts join the same active
   domain, so observing the selected endpoint also observes its neighbor. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `edge (← mkArrow tree (← mkArrow tree (mkSort Level.zero))) fun edge => do
  withLocalDeclD `left tree fun left => do
  withLocalDeclD `right tree fun right => do
  withLocalDeclD `connected (mkApp2 edge left right) fun _ => do
    let leftHeight := mkApp (mkConst ``Tree.height) left
    let view ← viewOf "consumer.contextActiveDomainObservation" left {} #[leftHeight]
    assertCanon "consumer.contextActiveDomainObservation" view.data
      "Tree|left\nNat|?₁\nTree|right\nNat|?₂\n\
       edge[Tree,Tree]:0,2\nheight[Tree,Nat]:0,1;2,3"

/- Observations parameterize fact relationalization. The source computation
    containing `height` remains `height`/`hAdd`/`hMul`/`lt`; WHNF must not expose
    the implementation-level `Nat.succ` constructor and its `n` field. -/
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `left tree fun left => do
  withLocalDeclD `right tree fun right => do
    let leftHeight := mkApp (mkConst ``Tree.height) left
    let rightHeight := mkApp (mkConst ``Tree.height) right
    let doubled ← mkAppM ``HMul.hMul #[mkRawNatLit 2, rightHeight]
    let oneMore ← mkAppM ``HAdd.hAdd #[doubled, mkRawNatLit 1]
    withLocalDeclD `branch (← mkAppM ``LT.lt #[oneMore, leftHeight]) fun _ => do
      let view ← viewOf "consumer.observationContext" left {} #[leftHeight]
      assertCanon "consumer.observationContext" view.data
        "Tree|left\nNat|?₁\nNat|?₂\nNat|?₃\nNat|2\nNat|?₄\nTree|right\nNat|1\n\
         hAdd[Nat,Nat,Nat]:3,7,2\nhMul[Nat,Nat,Nat]:4,5,3\n\
         height[Tree,Nat]:0,1;6,5\nlt[Nat,Nat]:2,1"
      assertMatchesReference "consumer.observationContext.reference" oneMore
        { functionGraphs := true, observations := #[leftHeight] }
      let scope ← scopeForAfaik view.afaik (← SelScope.ofType ``Tree) #[leftHeight]
      unless (scope.rels.get? "hAdd").map (·.2) == some (some 3) do
        throwError "consumer.observationContext: expected ternary hAdd"
      unless (scope.rels.get? "hMul").map (·.2) == some (some 3) do
        throwError "consumer.observationContext: expected ternary hMul"

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

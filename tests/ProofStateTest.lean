module

meta import SpytialLean.ProofState
meta import WalkCanon

open SpytialLean Lean Meta

/-! # Proof-state walker goldens

Contexts are built by hand (`withLocalDeclD` + fresh metavariables), so the
tests run headlessly — no tactic framework involved. -/

public inductive STree where
  | leaf (value : Nat)
  | node (left right : STree)

private meta def sTree : Expr := .const ``STree []

private meta def sLeaf (n : Nat) : Expr :=
  mkApp (mkConst ``STree.leaf) (mkRawNatLit n)

private meta def sNode (l r : Expr) : Expr :=
  mkApp2 (mkConst ``STree.node) l r

private meta def runState (goals : List MVarId) (subject? : Option Expr := none) :
    MetaM (Nat × WalkState) :=
  (walkProofState {} goals subject?).run {}

/-! ## A Prop hypothesis and the goal share atoms

`h : x < y` becomes the `lt` tuple, the goal `y < x` the `⊢ lt` tuple, and
both point at the same two atoms. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[x, y]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (← mkAppM ``LT.lt #[y, x]))
    let (skipped, st) ← runState [goal.mvarId!]
    unless skipped == 0 do throwError "state.lt: skipped {skipped}"
    assertCanon "state.lt" st.toDataInstance
      "Nat|x\nNat|y\nlt[Nat,Nat]:0,1\n⊢ lt[Nat,Nat]:1,0"

/-! ## A local relation names a relation too

`R` is a free variable, not a constant. `α : Type` and `R : α → α → Prop` are
vocabulary, not data — no atoms for them. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (mkApp2 R x y) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (mkApp2 R y x))
    let (skipped, st) ← runState [goal.mvarId!]
    unless skipped == 0 do throwError "state.fvarRel: skipped {skipped}"
    assertCanon "state.fvarRel" st.toDataInstance
      "α|x\nα|y\nR[α,α]:0,1\n⊢ R[α,α]:1,0"

/-! ## Non-decomposable Props are counted; a stuck goal is one Goal atom -/

#eval show Lean.Elab.TermElabM Unit from do
  let allTy ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkForallFVars #[n] (← mkAppM ``Eq #[n, n])
  withLocalDeclD `h allTy fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (mkConst ``True))
    let (skipped, st) ← runState [goal.mvarId!]
    unless skipped == 1 do throwError "state.skip: skipped {skipped}"
    assertCanon "state.skip" st.toDataInstance "Goal|True"

/-! ## Elaborator-known structure: an assigned metavariable draws as structure

The way `refine ⟨STree.node ?l ?r, ?h⟩` leaves the witness. The two sides of
the goal equation are open terms (fresh atoms each), but the holes `?l`/`?r`
are shared. -/

#eval show Lean.Elab.TermElabM Unit from do
  let l ← Meta.mkFreshExprMVar (some sTree) (userName := `l)
  let r ← Meta.mkFreshExprMVar (some sTree) (userName := `r)
  let w ← Meta.mkFreshExprMVar (some sTree)
  w.mvarId!.assign (sNode l r)
  let goal ← Meta.mkFreshExprMVar (some (← mkAppM ``Eq #[w, w]))
  let (skipped, st) ← runState [goal.mvarId!]
  unless skipped == 0 do throwError "state.assigned: skipped {skipped}"
  assertCanon "state.assigned" st.toDataInstance
    "STree|node\nSTree|?l\nSTree|?r\nSTree|node\n\
     left[STree,STree]:0,1;3,1\nright[STree,STree]:0,2;3,2\n⊢ =[STree,STree]:0,3"

/-! ## Refinement: `h : x = t` draws `x` as `t`

No opaque `x` atom, no `=` tuple — the structure is the hypothesis's
rendering. The goal's two `x` occurrences share the refined root. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[x, sNode (sLeaf 1) (sLeaf 2)]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (← mkAppM ``Eq #[x, x]))
    let (skipped, st) ← runState [goal.mvarId!]
    unless skipped == 0 do throwError "state.refined: skipped {skipped}"
    assertCanon "state.refined" st.toDataInstance
      "STree|node\nSTree|leaf\nNat|1\nSTree|leaf\nNat|2\n\
       left[STree,STree]:0,1\nright[STree,STree]:0,3\nvalue[STree,Nat]:1,2;3,4\n\
       ⊢ =[STree,STree]:0,0"

-- the reversed orientation `h : t = x` refines the same way
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[sLeaf 7, x]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (← mkAppM ``Eq #[x, x]))
    let (_, st) ← runState [goal.mvarId!]
    assertCanon "state.refined.rev" st.toDataInstance
      "STree|leaf\nNat|7\nvalue[STree,Nat]:0,1\n⊢ =[STree,STree]:0,0"

-- `h : x = y` merges two hypothesis variables into one atom
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `y sTree fun y => do
  withLocalDeclD `h (← mkAppM ``Eq #[x, y]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (← mkAppM ``Eq #[y, x]))
    let (_, st) ← runState [goal.mvarId!]
    assertCanon "state.refined.var" st.toDataInstance
      "STree|y\n⊢ =[STree,STree]:0,0"

-- a mutual chain terminates: the re-entered variable is the opaque leaf
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `y sTree fun y => do
  withLocalDeclD `h1 (← mkAppM ``Eq #[x, y]) fun _ => do
  withLocalDeclD `h2 (← mkAppM ``Eq #[y, x]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (mkConst ``True))
    let (skipped, st) ← runState [goal.mvarId!]
    unless skipped == 0 do throwError "state.refined.cycle: skipped {skipped}"
    assertCanon "state.refined.cycle" st.toDataInstance "STree|x\nGoal|True"

-- goals disagreeing about a variable (branches of `cases h : t`): the first
-- goal refines, the second keeps its equation as an `=` tuple against the
-- already-drawn atom — nothing is silently absorbed
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
    let g1 ← withLocalDeclD `h (← mkAppM ``Eq #[x, sLeaf 1]) fun _ => do
      Meta.mkFreshExprMVar (some (← mkAppM ``Eq #[x, x]))
    let g2 ← withLocalDeclD `h (← mkAppM ``Eq #[x, sLeaf 2]) fun _ => do
      Meta.mkFreshExprMVar (some (← mkAppM ``Eq #[x, x]))
    let (skipped, st) ← runState [g1.mvarId!, g2.mvarId!]
    unless skipped == 0 do throwError "state.refine.conflict: skipped {skipped}"
    assertCanon "state.refine.conflict" st.toDataInstance
      "STree|leaf\nNat|1\nSTree|leaf\nNat|2\n\
       =[STree,STree]:0,2\nvalue[STree,Nat]:0,1;2,3\n⊢ =[STree,STree]:0,0;0,0"

-- a variable drawn opaque by an earlier goal is not retroactively refined:
-- the later goal's equation stays an `=` tuple
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
    let g1 ← Meta.mkFreshExprMVar (some (← mkAppM ``Eq #[x, x]))
    let g2 ← withLocalDeclD `h (← mkAppM ``Eq #[x, sLeaf 1]) fun _ => do
      Meta.mkFreshExprMVar (some (mkConst ``True))
    let (_, st) ← runState [g1.mvarId!, g2.mvarId!]
    assertCanon "state.refine.late" st.toDataInstance
      "STree|x\nSTree|leaf\nNat|1\nGoal|True\n\
       =[STree,STree]:0,1\nvalue[STree,Nat]:1,2\n⊢ =[STree,STree]:0,0"

-- an equation between non-variables stays an `=` tuple
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `h (← mkAppM ``Eq #[sLeaf 1, sLeaf 2]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (mkConst ``True))
    let (_, st) ← runState [goal.mvarId!]
    assertCanon "state.eqTuple" st.toDataInstance
      "STree|leaf\nNat|1\nSTree|leaf\nNat|2\nGoal|True\n\
       =[STree,STree]:0,2\nvalue[STree,Nat]:0,1;2,3"

-- the fused walker and the two-pass reference agree on a refined walk
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
    let refinements : Std.HashMap FVarId Expr :=
      (({} : Std.HashMap FVarId Expr).insert x.fvarId! (sNode (sLeaf 1) (sLeaf 2)))
    assertMatchesReference "state.refined.oracle" x { refinements }

/-! ## Negative information -/

-- `h : x ≠ leaf 0` is a `≠` tuple; nothing claims the equality holds
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Ne #[x, sLeaf 0]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (mkConst ``True))
    let (skipped, st) ← runState [goal.mvarId!]
    unless skipped == 0 do throwError "state.ne: skipped {skipped}"
    assertCanon "state.ne" st.toDataInstance
      "STree|x\nSTree|leaf\nNat|0\nGoal|True\nvalue[STree,Nat]:1,2\n≠[STree,STree]:0,1"

-- `h : ¬ (R x y)` is a `¬R` tuple
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (mkApp (mkConst ``Not) (mkApp2 R x y)) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (mkConst ``True))
    let (skipped, st) ← runState [goal.mvarId!]
    unless skipped == 0 do throwError "state.notR: skipped {skipped}"
    assertCanon "state.notR" st.toDataInstance
      "α|x\nα|y\nGoal|True\n¬R[α,α]:0,1"

-- the definitional spelling `R x y → False` peels the same way
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (← mkArrow (mkApp2 R x y) (mkConst ``False)) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (mkConst ``True))
    let (_, st) ← runState [goal.mvarId!]
    assertCanon "state.arrowFalse" st.toDataInstance
      "α|x\nα|y\nGoal|True\n¬R[α,α]:0,1"

/-! ## Multiple goals share one diagram -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
    let g1 ← Meta.mkFreshExprMVar (some (← mkAppM ``LT.lt #[x, y]))
    let g2 ← Meta.mkFreshExprMVar (some (← mkAppM ``LT.lt #[y, x]))
    let (_, st) ← runState [g1.mvarId!, g2.mvarId!]
    assertCanon "state.twoGoals" st.toDataInstance
      "Nat|x\nNat|y\n⊢ lt[Nat,Nat]:0,1;1,0"

/-! ## Subject focus drops unrelated hypotheses, keeps the goal -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[n, n]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (← mkAppM ``Eq #[x, x]))
    let (_, st) ← runState [goal.mvarId!] (subject? := some x)
    assertCanon "state.subject" st.toDataInstance
      "STree|x\n⊢ =[STree,STree]:0,0"

/-! ## The scope predicts the walker's relations -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[x, y]) fun _ => do
    let goal ← Meta.mkFreshExprMVar (some (← mkAppM ``LT.lt #[y, x]))
    let scope ← proofStateScope [goal.mvarId!]
    unless scope.rels.get? "lt" == some (`_proofState, some 2) do
      throwError "scope: lt missing or wrong arity"
    unless scope.rels.get? "⊢ lt" == some (`_proofState, some 2) do
      throwError "scope: ⊢ lt missing or wrong arity"
    unless scope.types.contains ``Nat do
      throwError "scope: Nat missing"

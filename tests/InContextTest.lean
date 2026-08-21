module

meta import SpytialLean.InContext
meta import WalkCanon

open SpytialLean Lean Meta

/-! # In-context walker goldens

The subject is a value; the local context is the knowledge source. Contexts
are built by hand (`withLocalDeclD`, `withLetDecl`, fresh metavariables), so
the tests run headlessly — no tactic framework involved. -/

public inductive STree where
  | leaf (value : Nat)
  | node (left right : STree)

public def STree.depth : STree → Nat
  | .leaf _ => 0
  | .node l r => max l.depth r.depth + 1

public def STree.leftChild : STree → STree
  | .leaf _ => .leaf 0
  | .node l _ => l

public structure SPair where
  a : Nat
  b : Nat

private meta def sTree : Expr := .const ``STree []

private meta def sLeaf (n : Nat) : Expr :=
  mkApp (mkConst ``STree.leaf) (mkRawNatLit n)

private meta def sNode (l r : Expr) : Expr :=
  mkApp2 (mkConst ``STree.node) l r

private meta def runCtx (subject : Expr) (cfg : WalkConfig := {})
    (facts? : Option (Array FVarId) := none) (derive : Bool := false) :
    MetaM (Nat × WalkState) :=
  (walkInContext cfg subject facts? derive).run {}

/-! ## Facts anchor on the subject's atoms

`h : x < y` mentions the subject `x`, so it becomes the `lt` tuple — and `y`
enters the picture only because the fact brings it in. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[x, y]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.lt: skipped {skipped}"
    assertCanon "ctx.lt" st.toDataInstance
      "Nat|x\nNat|y\nlt[Nat,Nat]:0,1"

/-! ## A local relation names a relation too

`R` is a free variable, not a constant. Its type mentions only `α`, never the
subject, so `R` itself contributes no atom. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (mkApp2 R x y) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.fvarRel: skipped {skipped}"
    assertCanon "ctx.fvarRel" st.toDataInstance
      "α|x\nα|y\nR[α,α]:0,1"

/-! ## Subject-relevant Props that do not decompose are counted -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
    let allTy ← withLocalDeclD `n (mkConst ``Nat) fun n => do
      mkForallFVars #[n] (← mkAppM ``Eq #[x, x])
    withLocalDeclD `h allTy fun _ => do
      let (skipped, st) ← runCtx x
      unless skipped == 1 do throwError "ctx.skip: skipped {skipped}"
      assertCanon "ctx.skip" st.toDataInstance "STree|x"

/-! ## Elaborator-known structure

An assigned metavariable — the way `refine ⟨STree.node ?l ?r, ?h⟩` leaves the
witness — draws as structure with the still-open holes as atoms:
instantiate-then-walk. -/

#eval show Lean.Elab.TermElabM Unit from do
  let l ← Meta.mkFreshExprMVar (some sTree) (userName := `l)
  let r ← Meta.mkFreshExprMVar (some sTree) (userName := `r)
  let w ← Meta.mkFreshExprMVar (some sTree)
  w.mvarId!.assign (sNode l r)
  let (skipped, st) ← runCtx w
  unless skipped == 0 do throwError "ctx.assigned: skipped {skipped}"
  assertCanon "ctx.assigned" st.toDataInstance
    "STree|node\nSTree|?l\nSTree|?r\n\
     left[STree,STree]:0,1\nright[STree,STree]:0,2"

-- a `let` binding is elaborator-known structure as well: the bound variable
-- refines into its value
#eval show Lean.Elab.TermElabM Unit from do
  withLetDecl `t sTree (sNode (sLeaf 1) (sLeaf 2)) fun t => do
    let (skipped, st) ← runCtx t
    unless skipped == 0 do throwError "ctx.let: skipped {skipped}"
    assertCanon "ctx.let" st.toDataInstance
      "STree|node\nSTree|leaf\nNat|1\nSTree|leaf\nNat|2\n\
       left[STree,STree]:0,1\nright[STree,STree]:0,3\nvalue[STree,Nat]:1,2;3,4"

/-! ## Refinement: `h : x = t` draws `x` as `t`

No opaque `x` atom, no `=` tuple — the structure is the hypothesis's
rendering. -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[x, sNode (sLeaf 1) (sLeaf 2)]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.refined: skipped {skipped}"
    assertCanon "ctx.refined" st.toDataInstance
      "STree|node\nSTree|leaf\nNat|1\nSTree|leaf\nNat|2\n\
       left[STree,STree]:0,1\nright[STree,STree]:0,3\nvalue[STree,Nat]:1,2;3,4"

-- the reversed orientation `h : t = x` refines the same way
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[sLeaf 7, x]) fun _ => do
    let (_, st) ← runCtx x
    assertCanon "ctx.refined.rev" st.toDataInstance
      "STree|leaf\nNat|7\nvalue[STree,Nat]:0,1"

-- `h : x = y` merges two hypothesis variables into one atom
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `y sTree fun y => do
  withLocalDeclD `h (← mkAppM ``Eq #[x, y]) fun _ => do
    let (_, st) ← runCtx x
    assertCanon "ctx.refined.var" st.toDataInstance "STree|y"

-- a mutual chain terminates: the re-entered variable is the opaque leaf
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `y sTree fun y => do
  withLocalDeclD `h1 (← mkAppM ``Eq #[x, y]) fun _ => do
  withLocalDeclD `h2 (← mkAppM ``Eq #[y, x]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.refined.cycle: skipped {skipped}"
    assertCanon "ctx.refined.cycle" st.toDataInstance "STree|x"

-- two equations on one variable: the first refines, the second stays an
-- explicit `=` tuple against the refined structure — nothing is silently
-- absorbed
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h1 (← mkAppM ``Eq #[x, sLeaf 1]) fun _ => do
  withLocalDeclD `h2 (← mkAppM ``Eq #[x, sLeaf 2]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.refined.second: skipped {skipped}"
    assertCanon "ctx.refined.second" st.toDataInstance
      "STree|leaf\nNat|1\nSTree|leaf\nNat|2\n\
       =[STree,STree]:0,2\nvalue[STree,Nat]:0,1;2,3"

-- an injected refinement (caller-supplied `cfg.refinements`) wins over the
-- context: a disagreeing equation demotes to an `=` tuple …
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[x, sLeaf 2]) fun _ => do
    let cfg : WalkConfig :=
      { refinements := ({} : Std.HashMap FVarId Expr).insert x.fvarId! (sLeaf 1) }
    let (_, st) ← runCtx x (cfg := cfg)
    assertCanon "ctx.inject.conflict" st.toDataInstance
      "STree|leaf\nNat|1\nSTree|leaf\nNat|2\n\
       =[STree,STree]:0,2\nvalue[STree,Nat]:0,1;2,3"

-- … and an agreeing equation is absorbed: no duplicate `=` self-edge
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[x, sLeaf 1]) fun _ => do
    let cfg : WalkConfig :=
      { refinements := ({} : Std.HashMap FVarId Expr).insert x.fvarId! (sLeaf 1) }
    let (_, st) ← runCtx x (cfg := cfg)
    assertCanon "ctx.inject.agree" st.toDataInstance
      "STree|leaf\nNat|1\nvalue[STree,Nat]:0,1"

-- an equation whose sides are not plain variables stays an `=` tuple
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[sNode x x, sLeaf 1]) fun _ => do
    let (_, st) ← runCtx x
    assertCanon "ctx.eqTuple" st.toDataInstance
      "STree|x\nSTree|node\nSTree|leaf\nNat|1\n\
       =[STree,STree]:1,2\nleft[STree,STree]:1,0\nright[STree,STree]:1,0\n\
       value[STree,Nat]:2,3"

-- the fused walker and the two-pass reference agree on a refined walk
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
    let refinements : Std.HashMap FVarId Expr :=
      (({} : Std.HashMap FVarId Expr).insert x.fvarId! (sNode (sLeaf 1) (sLeaf 2)))
    assertMatchesReference "ctx.refined.oracle" x { refinements }

/-! ## Negative information -/

-- a negative fact draws only between values already in the world: `x ≠ y`
-- (both real) draws, against y's structure refined by its own equation;
-- nothing claims the equality holds
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `y sTree fun y => do
  withLocalDeclD `hy (← mkAppM ``Eq #[y, sLeaf 0]) fun _ => do
  withLocalDeclD `h (← mkAppM ``Ne #[x, y]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.ne: skipped {skipped}"
    assertCanon "ctx.ne" st.toDataInstance
      "STree|x\nSTree|leaf\nNat|0\nvalue[STree,Nat]:1,2\n≠[STree,STree]:0,1"

-- ruling a term out is not license to materialize it: `x ≠ leaf 0` against
-- a term not in the diagram is counted, not drawn
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Ne #[x, sLeaf 0]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 1 do throwError "ctx.ne.absent: skipped {skipped}"
    assertCanon "ctx.ne.absent" st.toDataInstance "STree|x"

-- `h : ¬ (R x y)` is a `¬R` tuple
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (mkApp (mkConst ``Not) (mkApp2 R x y)) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.notR: skipped {skipped}"
    assertCanon "ctx.notR" st.toDataInstance
      "α|x\nα|y\n¬R[α,α]:0,1"

-- the definitional spelling `R x y → False` peels the same way
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (← mkArrow (mkApp2 R x y) (mkConst ``False)) fun _ => do
    let (_, st) ← runCtx x
    assertCanon "ctx.arrowFalse" st.toDataInstance
      "α|x\nα|y\n¬R[α,α]:0,1"

/-! ## Function-graph equations: inside-knowledge attaches to the value -/

-- `depth x = 3` is a point of `depth`'s graph: one `depth` tuple attached
-- to the value. It also refutes `leaf` (depth of a leaf is 0, and 0 = 3
-- decides false), so `x` expands to the one surviving shape, `node`, with
-- holes for the fields
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[← mkAppM ``STree.depth #[x], mkRawNatLit 3]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.graph: skipped {skipped}"
    assertCanon "ctx.graph" st.toDataInstance
      "STree|node\nSTree|?left\nSTree|?right\nNat|3\n\
       depth[STree,Nat]:0,3\nleft[STree,STree]:0,1\nright[STree,STree]:0,2"

-- the reversed orientation reads the same way, and does NOT refine the
-- variable into a stuck term: `a = depth x` keeps `a` and draws the edge
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `a (mkConst ``Nat) fun a => do
  withLocalDeclD `h (← mkAppM ``Eq #[a, ← mkAppM ``STree.depth #[x]]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.graph.rev: skipped {skipped}"
    assertCanon "ctx.graph.rev" st.toDataInstance
      "STree|x\nNat|a\ndepth[STree,Nat]:0,1"

/-! ## Expansion by refutation: as knowledge grows, holes become atoms -/

-- the sketch: `depth x = 3` rules out `leaf`; `leftChild x = y` then
-- reduces on the `node` shape to `?left = y`, filling the hole and
-- absorbing the fact. x draws as a node with y on the left, a hole on the
-- right, and the depth arrow
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `y sTree fun y => do
  withLocalDeclD `hd (← mkAppM ``Eq #[← mkAppM ``STree.depth #[x], mkRawNatLit 3]) fun _ => do
  withLocalDeclD `hl (← mkAppM ``Eq #[← mkAppM ``STree.leftChild #[x], y]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.expand.fill: skipped {skipped}"
    assertCanon "ctx.expand.fill" st.toDataInstance
      "STree|node\nSTree|y\nSTree|?right\nNat|3\n\
       depth[STree,Nat]:0,3\nleft[STree,STree]:0,1\nright[STree,STree]:0,2"

-- a structure has one constructor, so a projection fact alone expands it:
-- `p.a = 5` gives ⟨5, ?b⟩
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `p (mkConst ``SPair) fun p => do
  withLocalDeclD `h (← mkAppM ``Eq #[← mkAppM ``SPair.a #[p], mkRawNatLit 5]) fun _ => do
    let (skipped, st) ← runCtx p
    unless skipped == 0 do throwError "ctx.expand.struct: skipped {skipped}"
    assertCanon "ctx.expand.struct" st.toDataInstance
      "SPair|mk\nNat|5\nNat|?b\na[SPair,Nat]:0,1\nb[SPair,Nat]:0,2"

-- refutation needs a decidable ground statement: `x ≠ y` (no DecidableEq,
-- abstract y) refutes nothing, so nothing expands
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `y sTree fun y => do
  withLocalDeclD `h (← mkAppM ``Ne #[x, y]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.expand.none: skipped {skipped}"
    assertCanon "ctx.expand.none" st.toDataInstance
      "STree|x\nSTree|y\n≠[STree,STree]:0,1"

/-! ## Conjunctions split into their parts -/

-- `∧` glues facts together; each part draws on its own, nested included
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (← mkAppM ``And #[mkApp2 R x y,
      ← mkAppM ``And #[mkApp2 R y x, mkApp2 R x x]]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.and: skipped {skipped}"
    assertCanon "ctx.and" st.toDataInstance
      "α|x\nα|y\nR[α,α]:0,1;1,0;0,0"

-- an equation inside an `∧` still refines; the other part still draws
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `y sTree fun y => do
  withLocalDeclD `h (← mkAppM ``And #[← mkAppM ``Eq #[x, sLeaf 1],
      ← mkAppM ``Ne #[x, y]]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.and.refine: skipped {skipped}"
    assertCanon "ctx.and.refine" st.toDataInstance
      "STree|leaf\nNat|1\nSTree|y\nvalue[STree,Nat]:0,1\n≠[STree,STree]:0,2"

-- a part that does not mention the subject is ignored, not counted
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `n a fun n => do
  withLocalDeclD `h (← mkAppM ``And #[mkApp2 R x y, mkApp2 R n n]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.and.partial: skipped {skipped}"
    assertCanon "ctx.and.partial" st.toDataInstance
      "α|x\nα|y\nR[α,α]:0,1"

-- `∨` cannot split — one side holds, but which is unknown: counted
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (← mkAppM ``Or #[mkApp2 R x y, mkApp2 R y x]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 1 do throwError "ctx.or: skipped {skipped}"
    assertCanon "ctx.or" st.toDataInstance "α|x"

/-! ## Hypotheses not mentioning the subject are not this diagram's business -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[n, n]) fun _ => do
    let (skipped, st) ← runCtx x
    unless skipped == 0 do throwError "ctx.unrelated: skipped {skipped}"
    assertCanon "ctx.unrelated" st.toDataInstance "STree|x"

/-! ## `using`: the caller picks the facts -/

-- a listed fact draws even when it does not mention the subject
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `n (mkConst ``Nat) fun n => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[n, n]) fun h => do
    let (skipped, st) ← runCtx x (facts? := some #[h.fvarId!])
    unless skipped == 0 do throwError "ctx.using.include: skipped {skipped}"
    assertCanon "ctx.using.include" st.toDataInstance
      "STree|x\nNat|n\nlt[Nat,Nat]:1,1"

-- an empty list draws no facts at all — even ones the automatic selection
-- would draw
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[x, y]) fun _ => do
    let (skipped, st) ← runCtx x (facts? := some #[])
    unless skipped == 0 do throwError "ctx.using.none: skipped {skipped}"
    assertCanon "ctx.using.none" st.toDataInstance "Nat|x"

-- refinements are not facts: a listed equation consumed as a refinement
-- still emits nothing, and the refinement applies with or without `using`
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x sTree fun x => do
  withLocalDeclD `h (← mkAppM ``Eq #[x, sLeaf 1]) fun h => do
    let (skipped, st) ← runCtx x (facts? := some #[h.fvarId!])
    unless skipped == 0 do throwError "ctx.using.consumed: skipped {skipped}"
    assertCanon "ctx.using.consumed" st.toDataInstance
      "STree|leaf\nNat|1\nvalue[STree,Nat]:0,1"

/-! ## Derivation: universal facts put to work -/

-- symmetry applied to a drawn fact: `R x y` proves `R y x`, and both draw
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h (mkApp2 R x y) fun _ => do
    let symTy ← withLocalDeclD `p a fun p => withLocalDeclD `q a fun q => do
      mkForallFVars #[p, q] (← mkArrow (mkApp2 R p q) (mkApp2 R q p))
    withLocalDeclD `hs symTy fun _ => do
      let (skipped, st) ← runCtx x (derive := true)
      unless skipped == 0 do throwError "ctx.derive: skipped {skipped}"
      assertCanon "ctx.derive" st.toDataInstance
        "α|x\nα|y\nR[α,α]:0,1;1,0"

-- transitivity chains: from R x y and R y x it proves R x x (drawn) and
-- R y y (also proved, but not about the subject, so not drawn — derived
-- facts follow the same rules as any fact)
#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `α (mkSort Level.one) fun a => do
  withLocalDeclD `R (← mkArrow a (← mkArrow a (mkSort Level.zero))) fun R => do
  withLocalDeclD `x a fun x => do
  withLocalDeclD `y a fun y => do
  withLocalDeclD `h1 (mkApp2 R x y) fun _ => do
  withLocalDeclD `h2 (mkApp2 R y x) fun _ => do
    let transTy ← withLocalDeclD `p a fun p => withLocalDeclD `q a fun q => do
      withLocalDeclD `r a fun r => do
        mkForallFVars #[p, q, r] (← mkArrow (mkApp2 R p q)
          (← mkArrow (mkApp2 R q r) (mkApp2 R p r)))
    withLocalDeclD `ht transTy fun _ => do
      let (_, st) ← runCtx x (derive := true)
      assertCanon "ctx.derive.chain" st.toDataInstance
        "α|x\nα|y\nR[α,α]:0,1;1,0;0,0"

/-! ## The scope is the subject type's, extended with the fact vocabulary -/

#eval show Lean.Elab.TermElabM Unit from do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `h (← mkAppM ``LT.lt #[x, y]) fun _ => do
    let scope ← scopeInContext x
    unless scope.root == ``Nat do
      throwError "scope: root is {scope.root}, expected Nat"
    unless (scope.rels.get? "lt").map (·.2) == some (some 2) do
      throwError "scope: lt missing or wrong arity"
    unless scope.types.contains ``Nat do
      throwError "scope: Nat missing"

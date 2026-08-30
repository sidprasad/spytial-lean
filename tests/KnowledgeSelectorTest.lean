import KnowledgeSelectorFixture

open SpytialLean Lean Meta Elab Tactic

set_option spytial.source false
set_option linter.unusedVariables false

/-! Knowledge selectors match extracted evidence, not executable values. -/

private meta def viewOf (root : Expr) : MetaM ContextView := do
  let (_, some view) ← wdykInContext root {} { mechanisms := #[.simp] }
    | throwError "expected a consistent context view"
  return view

private meta def assertSelection (view : ContextView) (predicate : Expr)
    (expected : Array (Array String)) : MetaM Unit := do
  let selected ← evalKnownRel
    { datum := view.datum, di := view.data, prov := view.prov,
      knowledge? := some (← view.selectorKnowledge) } predicate
  let labels := selected.map fun tuple => tuple.map fun id =>
    (view.data.atoms.find? fun atom => atom.id == id).map (·.label) |>.getD "missing atom"
  unless labels == expected do
    throwError "expected {repr expected}, got {repr labels}"

syntax "knowledge_wire_spec " term (" with " "[" spytial_op,*,? "]")? : tactic

elab_rules : tactic
  | `(tactic| knowledge_wire_spec $subject:term $[with [$ops,*]]?) => withMainContext do
    let subject ← Term.elabTerm subject none
    Term.synthesizeSyntheticMVarsNoPostponing
    let (props, _) ← spytialInContextProps (← instantiateMVars subject)
      (ops.map fun ops => ops.getElems)
    logInfo ((props.getObjValAs? String "cndSpec").toOption.getD "missing spec")

-- The attached spec selects the symbolic tree from its height fact.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
example (t : KnowledgeTree) (h : t.height = 3) : True := by
  knowledge_wire_spec t
  trivial

-- The use-site form has the same interpretation.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
example (t : KnowledgeTree) (h : t.height = 3) : True := by
  knowledge_wire_spec t with [hideAtom known (fun n : KnowledgeTree => n.height = 3)]
  trivial

/-- info: {"constraints": [{"hideAtom": {"selector": "none"}}]} -/
#guard_msgs in
example (t : KnowledgeTree) : True := by
  knowledge_wire_spec t
  trivial

-- Real tactic surface, including observations and selector composition.
example (t : KnowledgeTree) (h : t.height = 3) : True := by
  spytial t observing [KnowledgeTree.height] with [
    atomStyle known (fun n : KnowledgeTree => n.height = 3) & KnowledgeTree
      (fillStyle "#dbeafe")
  ]
  trivial

-- Captured proof-local parameters and undecidable predicates are allowed.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
example (P : Nat → Prop) (x : Nat) (h : P x) : True := by
  knowledge_wire_spec x with [hideAtom known (P)]
  trivial

-- Resolution also reaches leaves inside binder domains and formulas.
example (P : Nat → Prop) (x : Nat) (h : P x) : True := by
  spytial x with [hideAtom { n : known (P) | n in known (P) }]
  trivial

example (edge : Nat → Nat → Prop) (x y : Nat) (h : edge x y) : True := by
  spytial x with [inferredEdge path known (edge)]
  trivial

-- Neither a predicate nor its negation is inferred from absence of evidence.
#eval show TermElabM Unit from do
  withLocalDeclD `P (← mkArrow (mkConst ``Nat) (mkSort .zero)) fun P => do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let notP ← withLocalDeclD `n (mkConst ``Nat) fun n => do
      mkLambdaFVars #[n] (← mkAppM ``Not #[mkApp P n])
    let unknown ← viewOf x
    assertSelection unknown P #[]
    assertSelection unknown notP #[]
    withLocalDeclD `negative (mkApp notP x) fun _ => do
      let view ← viewOf x
      assertSelection view P #[]
      assertSelection view notP #[#["x"]]

-- Other represented endpoints do not manufacture additional tuples or transitivity.
#eval show TermElabM Unit from do
  withLocalDeclD `α (mkSort .one) fun α => do
  withLocalDeclD `R (← mkArrow α (← mkArrow α (mkSort .zero))) fun R => do
  withLocalDeclD `x α fun x => do
  withLocalDeclD `y α fun y => do
  withLocalDeclD `z α fun z => do
  withLocalDeclD `hxy (mkApp2 R x y) fun _ => do
  withLocalDeclD `hyz (mkApp2 R y z) fun _ => do
    assertSelection (← viewOf x) R #[#["x", "y"], #["y", "z"]]

-- Witness terms retain the same atom at both ends of an existential path.
#eval show TermElabM Unit from do
  withLocalDeclD `α (mkSort .one) fun α => do
  withLocalDeclD `edge (← mkArrow α (← mkArrow α (mkSort .zero))) fun edge => do
  withLocalDeclD `source α fun source => do
  withLocalDeclD `target α fun target => do
    let route ← withLocalDeclD `middle α fun middle => do
      let body ← mkAppM ``And #[mkApp2 edge source middle, mkApp2 edge middle target]
      mkAppM ``Exists #[← mkLambdaFVars #[middle] body]
    withLocalDeclD `route route fun _ => do
      assertSelection (← viewOf source) edge #[#["•₁", "target"], #["source", "•₁"]]

-- Refining x changes its picture but does not lose the term used by h : P x.
#eval show TermElabM Unit from do
  let tree := mkConst ``KnowledgeTree
  withLocalDeclD `P (← mkArrow tree (mkSort .zero)) fun P => do
  withLocalDeclD `x tree fun x => do
  withLocalDeclD `value (← mkEq x (mkConst ``KnowledgeTree.leaf)) fun _ => do
  withLocalDeclD `h (mkApp P x) fun _ => do
  withLocalDeclD `also (mkApp P (mkConst ``KnowledgeTree.leaf)) fun _ => do
    assertSelection (← viewOf x) P #[#["leaf"]]

-- Definitional matching does not combine separate facts into a conjunction.
#eval show TermElabM Unit from do
  let nat := mkConst ``Nat
  withLocalDeclD `P (← mkArrow nat (mkSort .zero)) fun P => do
  withLocalDeclD `Q (← mkArrow nat (mkSort .zero)) fun Q => do
  withLocalDeclD `x nat fun x => do
  withLocalDeclD `hp (mkApp P x) fun _ => do
  withLocalDeclD `hq (mkApp Q x) fun _ => do
    let both ← withLocalDeclD `n nat fun n => do
      mkLambdaFVars #[n] (← mkAppM ``And #[mkApp P n, mkApp Q n])
    assertSelection (← viewOf x) both #[]

-- The type check uses Lean types, not their shared short display name. Synthetic
-- atoms with no term, and terms containing holes, are excluded even from a constant predicate.
#eval show TermElabM Unit from do
  withLocalDeclD `α (mkSort .one) fun α => do
  withLocalDeclD `α (mkSort .one) fun β => do
  withLocalDeclD `P (← mkArrow α (mkSort .zero)) fun P => do
  withLocalDeclD `x α fun x => do
  withLocalDeclD `y β fun y => do
  withLocalDeclD `h (mkApp P x) fun _ => do
    let view ← viewOf x
    let hole ← mkFreshExprMVar α
    let data := { view.data with atoms := view.data.atoms ++ #[
      { id := "otherType", type := "α", label := "y" },
      { id := "unbacked", type := "α", label := "unbacked" },
      { id := "hole", type := "α", label := "hole" }] }
    let terms := view.terms ++ #[(y, "otherType"), (hole, "hole")]
    let constant ← withLocalDeclD `n α fun n => mkLambdaFVars #[n] (mkApp P x)
    assertSelection { view with data, terms } constant #[#["x"]]
    if ← hole.mvarId!.isAssigned then throwError "selector assigned a user's hole"

-- Bound the work before enumeration, including cases where nothing would match.
/--
error: this `known` selector requires 1002001 fact comparisons, over the limit of 1000000;
use a narrower predicate or inspection
-/
#guard_msgs (whitespace := lax) in
#eval show TermElabM Unit from do
  let nat := mkConst ``Nat
  withLocalDeclD `R (← mkArrow nat (← mkArrow nat (mkSort .zero))) fun R => do
  withLocalDeclD `x nat fun x => do
  withLocalDeclD `h (mkApp2 R x x) fun _ => do
    let view ← viewOf x
    let knowledge ← view.selectorKnowledge
    let repeated := { knowledge with terms := Array.replicate 1001 (x, "atom_0") }
    discard <| evalKnownRel
      { datum := view.datum, di := view.data, prov := view.prov, knowledge? := some repeated } R

-- Commands have no extraction: an attached selector must not become silently empty.
/--
error: a `known` selector needs extracted proof-context knowledge;
use it with the `spytial` tactic, not `#spytial`
-/
#guard_msgs (whitespace := lax) in
#spytial KnowledgeTree.leaf

/--
error: a `known` selector must return `Prop`;
use `lean` for executable Boolean predicates or `Spytial.Sel` programs
-/
#guard_msgs (whitespace := lax) in
example (n : Nat) : True := by
  spytial n with [hideAtom known (fun x : Nat => x == 3)]
  trivial

-- Whole-value selectors keep the hard error, including in attached specs.
structure WholeBox where
  values : List Nat
  deriving BEq

def wholeValues : Spytial.Sel WholeBox Nat := ⟨fun box => box.values⟩
spytial_spec WholeBox [hideAtom lean (wholeValues)]

/--
error: a `Spytial.Sel` runs on the whole value being drawn, but the context does not determine
that value; a predicate selects among the individually known values instead
-/
#guard_msgs (whitespace := lax) in
example (box : WholeBox) : True := by
  spytial box
  trivial

module

public import SpytialTests.KnowledgeSelectorFixture
public meta import SpytialTests.KnowledgeSelectorFixture

public section

open SpytialLean Lean Meta Elab Tactic

set_option spytial.source false
set_option linter.unusedVariables false

/-! The same Lean predicates select represented atoms in every inspection context. -/

private meta def viewOf (root : Expr) : MetaM ContextView := do
  let (_, some view) ← wdykInContext root {} { mechanisms := #[.simp] }
    | throwError "expected a consistent context view"
  return view

private meta def assertSelection (view : ContextView) (predicate : Expr)
    (expected : Array (Array String)) : MetaM Unit := do
  let selected ← evalLeanRel
    { datum := view.datum, di := view.data, prov := view.prov,
      evidence := view.evidence } predicate
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
  knowledge_wire_spec t with [hideAtom lean (fun n : KnowledgeTree => n.height = 3)]
  trivial

/-- info: {"constraints": [{"hideAtom": {"selector": "none"}}]} -/
#guard_msgs in
example (t : KnowledgeTree) : True := by
  knowledge_wire_spec t
  trivial

-- Real tactic surface, including observations and selector composition.
example (t : KnowledgeTree) (h : t.height = 3) : True := by
  spytial t observing [KnowledgeTree.height] with [
    atomStyle lean (fun n : KnowledgeTree => n.height = 3) & KnowledgeTree
      (fillStyle "#dbeafe")
  ]
  trivial

-- Captured proof-local parameters and undecidable predicates are allowed.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
example (P : Nat → Prop) (x : Nat) (h : P x) : True := by
  knowledge_wire_spec x with [hideAtom lean (P)]
  trivial

-- Resolution also reaches leaves inside binder domains and formulas.
example (P : Nat → Prop) (x : Nat) (h : P x) : True := by
  spytial x with [hideAtom { n : lean (P) | n in lean (P) }]
  trivial

example (edge : Nat → Nat → Prop) (x y : Nat) (h : edge x y) : True := by
  spytial x with [inferredEdge path lean (edge)]
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
      assertSelection (← viewOf source) edge #[#["?₁", "target"], #["source", "?₁"]]

-- Refining x changes its picture but does not lose the term used by h : P x.
#eval show TermElabM Unit from do
  let tree := mkConst ``KnowledgeTree
  withLocalDeclD `P (← mkArrow tree (mkSort .zero)) fun P => do
  withLocalDeclD `x tree fun x => do
  withLocalDeclD `value (← mkEq x (mkConst ``KnowledgeTree.leaf)) fun _ => do
  withLocalDeclD `h (mkApp P x) fun _ => do
  withLocalDeclD `also (mkApp P (mkConst ``KnowledgeTree.leaf)) fun _ => do
    assertSelection (← viewOf x) P #[#["leaf"]]

-- Bounded simplification can combine independently established predicates.
#eval show TermElabM Unit from do
  let nat := mkConst ``Nat
  withLocalDeclD `P (← mkArrow nat (mkSort .zero)) fun P => do
  withLocalDeclD `Q (← mkArrow nat (mkSort .zero)) fun Q => do
  withLocalDeclD `x nat fun x => do
  withLocalDeclD `hp (mkApp P x) fun _ => do
  withLocalDeclD `hq (mkApp Q x) fun _ => do
    let both ← withLocalDeclD `n nat fun n => do
      mkLambdaFVars #[n] (← mkAppM ``And #[mkApp P n, mkApp Q n])
    assertSelection (← viewOf x) both #[#["x"]]

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
    let terms := view.evidence.terms ++ #[(y, "otherType"), (hole, "hole")]
    let constant ← withLocalDeclD `n α fun n => mkLambdaFVars #[n] (mkApp P x)
    assertSelection { view with data, evidence := { view.evidence with terms } } constant #[#["x"]]
    if ← hole.mvarId!.isAssigned then throwError "selector assigned a user's hole"

-- Bound symbolic enumeration before checking any tuple.
/--
error: this Lean predicate requires 1002001 candidate/evidence checks, over the limit of 1000000;
use a narrower predicate or inspection
-/
#guard_msgs (whitespace := lax) in
#eval show TermElabM Unit from do
  let nat := mkConst ``Nat
  withLocalDeclD `R (← mkArrow nat (← mkArrow nat (mkSort .zero))) fun R => do
  withLocalDeclD `x nat fun x => do
  withLocalDeclD `h (mkApp2 R x x) fun _ => do
    let view ← viewOf x
    let atoms := (Array.range 1001).map fun i =>
      { id := s!"atom_{i}", type := "Nat", label := s!"x{i}" : JsonAtom }
    let evidence := { view.evidence with terms := atoms.map fun atom => (x, atom.id) }
    discard <| evalLeanRel
      { datum := x, di := { atoms, relations := #[] }, prov := {}, evidence } R

-- The imported attached predicate is also valid in command mode.
#spytial KnowledgeTree.leaf

/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
#spytial.spec threeHigh with [hideAtom lean (hasHeightThree)]

-- The attached spec itself is usable on a fully computed datum as well.
#spytial threeHigh

-- Bool-valued predicates can use the same contextual equalities.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
example (t : KnowledgeTree) (h : t.height = 3) : True := by
  knowledge_wire_spec t with [hideAtom lean (fun n : KnowledgeTree => n.height == 3)]
  trivial

-- Inspect during execution: the branch assumption establishes the property,
-- although the argument and the result are still symbolic trees.
def inspectHeightBranch (t : KnowledgeTree) : KnowledgeTree := by
  spytial t
  exact if h : t.height = 3 then by
    spytial t with [hideAtom lean (hasHeightThree)]
    exact t
  else t

-- Selectors can capture a local threshold without requiring a concrete tree.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
example (t : KnowledgeTree) (k : Nat) (h : t.height = k) : True := by
  knowledge_wire_spec t with [hideAtom lean (fun n : KnowledgeTree => n.height = k)]
  trivial

-- Computation with symbolic children and context equalities: the parent has
-- height 3 even though neither child is a closed value. Observation equations
-- survive relationalization and are sufficient evidence on their own.
#eval show TermElabM Unit from do
  let tree := mkConst ``KnowledgeTree
  let height := mkConst ``KnowledgeTree.height
  withLocalDeclD `left tree fun left => do
  withLocalDeclD `right tree fun right => do
  withLocalDeclD `hl (← mkEq (mkApp height left) (mkNatLit 2)) fun _ => do
  withLocalDeclD `hr (← mkEq (mkApp height right) (mkNatLit 1)) fun _ => do
    let root := mkApp2 (mkConst ``KnowledgeTree.node) left right
    let (_, some view) ← wdykInContext root {} { mechanisms := #[.simp] } #[mkApp height root]
      | throwError "expected an observed tree"
    let predicate := mkConst ``hasHeightThree
    assertSelection view predicate #[#["node"]]
    -- The selected tuple refers to the same root whose displayed height is 3.
    let some relation := view.data.relations.find? (·.name == "height")
      | throwError "missing height relation"
    let some point := relation.tuples.find? (·.atoms[0]? == some view.inspection.root)
      | throwError "missing root height"
    let some result := view.data.atoms.find? (fun atom => point.atoms[1]? == some atom.id)
      | throwError "missing height value"
    unless result.label == "3" do throwError "parent height was not evaluated"
    let observationProofs := view.evidence.proofs.filter fun proof =>
      !view.afaik.facts.any (·.proof.equal proof)
    unless !observationProofs.isEmpty do throwError "lost observation proofs"
    assertSelection { view with evidence := { view.evidence with proofs := observationProofs } }
      predicate #[#["node"]]

-- The same partial computation also works without requesting a height relation.
#eval show TermElabM Unit from do
  let tree := mkConst ``KnowledgeTree
  let height := mkConst ``KnowledgeTree.height
  withLocalDeclD `left tree fun left => do
  withLocalDeclD `right tree fun right => do
  withLocalDeclD `hl (← mkEq (mkApp height left) (mkNatLit 2)) fun _ => do
  withLocalDeclD `hr (← mkEq (mkApp height right) (mkNatLit 1)) fun _ => do
    let root := mkApp2 (mkConst ``KnowledgeTree.node) left right
    assertSelection (← viewOf root) (mkConst ``hasHeightThree) #[#["node"]]

-- Evidence can mention values outside the datum, but cannot make them candidates.
#eval show TermElabM Unit from do
  withLocalDeclD `P (← mkArrow (mkConst ``Nat) (mkSort .zero)) fun P => do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `hx (mkApp P x) fun hx => do
  withLocalDeclD `hy (mkApp P y) fun hy => do
    let view ← viewOf x
    let data := { view.data with atoms := view.data.atoms.filter (·.id == view.inspection.root) }
    let evidence := { view.evidence with
      terms := view.evidence.terms.push (y, "not-in-datum"), proofs := #[hx, hy] }
    assertSelection { view with data, evidence } P #[#["x"]]

-- A single predicate combines compiled matches on closed values with
-- proof-backed matches on symbolic values, in the datum's atom order.
#eval show TermElabM Unit from do
  let tree := mkConst ``KnowledgeTree
  withLocalDeclD `child tree fun child => do
  withLocalDeclD `h (← mkEq (mkApp (mkConst ``KnowledgeTree.height) child) (mkNatLit 0))
      fun _ => do
    let root := mkApp2 (mkConst ``KnowledgeTree.node) (mkConst ``KnowledgeTree.leaf) child
    let predicate ← withLocalDeclD `node tree fun node => do
      mkLambdaFVars #[node] (← mkEq (mkApp (mkConst ``KnowledgeTree.height) node) (mkNatLit 0))
    assertSelection (← viewOf root) predicate #[#["leaf"], #["child"]]

-- Layout predicates do not change either inspection dataset.
#eval show TermElabM Unit from do
  withLocalDeclD `t (mkConst ``KnowledgeTree) fun t => do
  withLocalDeclD `h (← mkEq (mkApp (mkConst ``KnowledgeTree.height) t) (mkNatLit 3))
      fun _ => do
    let (plain, _) ← spytialInContextProps t (some #[])
    let op ← ofExcept <| Parser.runParserCategory (← getEnv) `spytial_op
      "hideAtom lean (hasHeightThree)"
    let (selected, _) ← spytialInContextProps t (some #[⟨op⟩])
    let plainData ← ofExcept (plain.getObjVal? "dataInstance")
    let selectedData ← ofExcept (selected.getObjVal? "dataInstance")
    let plainInspection ← ofExcept (plain.getObjVal? "inspection")
    let selectedInspection ← ofExcept (selected.getObjVal? "inspection")
    unless plainData == selectedData && plainInspection == selectedInspection do
      throwError "selector changed the relationalized datum"

-- Boolean negation must not turn an unknown test into a match.
#eval show TermElabM Unit from do
  withLocalDeclD `test (← mkArrow (mkConst ``Nat) (mkConst ``Bool)) fun test => do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let negative ← withLocalDeclD `n (mkConst ``Nat) fun n =>
      mkLambdaFVars #[n] (mkApp (mkConst ``Bool.not) (mkApp test n))
    assertSelection (← viewOf x) test #[]
    assertSelection (← viewOf x) negative #[]
    withLocalDeclD `h (← mkEq (mkApp test x) (mkConst ``Bool.false)) fun _ => do
      assertSelection (← viewOf x) test #[]
      assertSelection (← viewOf x) negative #[#["x"]]

-- Coarse identity does not turn equality of drawing keys into Lean equality.
structure ParityNode where
  key : Nat

instance : SpytialIdentity ParityNode :=
  ⟨.identity fun node => .ofNat (node.key % 2), none⟩

#eval show TermElabM Unit from do
  let one := mkApp (mkConst ``ParityNode.mk) (mkNatLit 1)
  let three := mkApp (mkConst ``ParityNode.mk) (mkNatLit 3)
  let root ← mkAppM ``Prod.mk #[one, three]
  let (data, prov, evidence) ← relationalizeWithEvidence root
  unless (data.atoms.filter (·.type == "ParityNode")).size == 1 do
    throwError "identity should have merged the two nodes"
  withLocalDeclD `target (mkConst ``Nat) fun target => do
  withLocalDeclD `targetIsThree (← mkEq target (mkNatLit 3)) fun proof => do
    let predicate ← withLocalDeclD `node (mkConst ``ParityNode) fun node => do
      mkLambdaFVars #[node] (← mkEq (mkApp (mkConst ``ParityNode.key) node) target)
    let selected ← evalLeanRel
      { datum := root, di := data, prov, evidence := { evidence with proofs := #[proof] } }
      predicate
    unless selected.isEmpty do throwError "selector matched a non-representative class member"

-- Occurrence identity stays distinct even when the predicate matches equal values.
structure OccurrenceNode where
  key : Nat

instance : SpytialIdentity OccurrenceNode := .asWritten

#eval show TermElabM Unit from do
  let one := mkApp (mkConst ``OccurrenceNode.mk) (mkNatLit 1)
  let root ← mkAppM ``Prod.mk #[one, one]
  let (data, prov, evidence) ← relationalizeWithEvidence root
  let predicate ← withLocalDeclD `node (mkConst ``OccurrenceNode) fun node => do
    mkLambdaFVars #[node] (← mkEq (mkApp (mkConst ``OccurrenceNode.key) node) (mkNatLit 1))
  let selected ← evalLeanRel { datum := root, di := data, prov, evidence } predicate
  unless selected.size == 2 && selected[0]! != selected[1]! do
    throwError "selector collapsed equal asWritten occurrences"

-- An unresolved selector itself is rejected without filling the user's hole.
#eval show TermElabM Unit from do
  let root := mkNatLit 1
  let (data, prov, evidence) ← relationalizeWithEvidence root
  let hole ← mkFreshExprMVar (← mkArrow (mkConst ``Nat) (mkSort .zero))
  let rejected ← try
    discard <| evalLeanRel { datum := root, di := data, prov, evidence } hole
    pure false
  catch _ => pure true
  unless rejected do throwError "accepted an unresolved selector"
  if ← hole.mvarId!.isAssigned then throwError "selector assigned the user's predicate hole"

-- A backed custom atom can use compiled predicates without a legacy provenance
-- entry. A synthetic atom without a term was excluded in the earlier test.
#eval show TermElabM Unit from do
  let root := mkNatLit 3
  let data : JsonDataInstance := {
    atoms := #[{ id := "custom-root", type := "Nat", label := "custom" }], relations := #[] }
  let evidence : SelectorEvidence := { terms := #[(root, "custom-root")] }
  let predicate ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkLambdaFVars #[n] (← mkEq n root)
  let selected ← evalLeanRel { datum := root, di := data, prov := {}, evidence } predicate
  unless selected == #[#["custom-root"]] do throwError "missed a backed custom root"

opaque hiddenProperty (n : Nat) : Prop := n = 3

-- Classical decidability is not an executable decision procedure. It must
-- not block a predicate already supported by a retained fact.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
example (h : hiddenProperty 3) : True := by
  classical
  knowledge_wire_spec (3 : Nat) with [hideAtom lean (hiddenProperty)]
  trivial

-- Nor may a local Decidable instance escape into the compiled evaluator.
/-- info: {"constraints": [{"hideAtom": {"selector": "`atom_0"}}]} -/
#guard_msgs in
example [DecidablePred hiddenProperty] (h : hiddenProperty 3) : True := by
  knowledge_wire_spec (3 : Nat) with [hideAtom lean (hiddenProperty)]
  trivial

-- With neither a body nor evidence, the opaque predicate remains undetermined.
/-- info: {"constraints": [{"hideAtom": {"selector": "none"}}]} -/
#guard_msgs in
open scoped Classical in
#spytial.spec (3 : Nat) with [hideAtom lean (hiddenProperty)]

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

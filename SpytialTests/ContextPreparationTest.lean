import SpytialLean
import Aesop.Frontend.Saturate

open Lean Meta Elab Tactic SpytialLean

set_option linter.unusedVariables false

/-! These checks exercise the adapter's trust and stopping boundaries. The existing inspection,
selector, explorer, and closed-value suites pin the resulting diagrams and program behavior. -/

-- Existential chaining already works in ordinary Aesop saturation, without any Spytial code.
set_option aesop.dev.statefulForward true in
example (P Q R : Nat → Prop) (S : Prop) (a : Nat) (hp : P a)
    (witness : ∀ n, P n → ∃ w, Q w ∧ R w)
    (finish : ∀ w, Q w → R w → S) : S := by
  saturate 8 [witness, Classical.choose_spec, And.left, And.right, finish]
  assumption

private meta def assertProofs (context : InspectionContext) (claims : Array Expr) : MetaM Unit := do
  -- Deliberately check in the caller's scope, not an enriched Aesop context.
  let original ← getLCtx
  for proof in context.proofs do
    if proof.hasMVar || proof.hasLevelMVar then throwError "proof contains a metavariable"
    if (proof.find? fun e => e.isFVar && !original.contains e.fvarId!).isSome then
      throwError "a temporary hypothesis escaped"
    discard <| checkInspectionProof (← inferType proof) proof
  for claim in claims do
    unless ← context.proofs.anyM (fun proof => do isDefEq (← inferType proof) claim) do
      throwError "missing expected evidence for {claim}"

/-- Match `fyi`: preserve a bare local rule, including its implicit instance binders. -/
private meta def elabRule (rule : Syntax) : TermElabM Expr := do
  if rule.isIdent then
    if let some e@(.fvar _) ← Term.resolveId? rule then return e
  Term.elabTerm rule none

elab "check_preparation " root:term " using " "[" rules:term,* "]"
    " proves " "[" claims:term,* "]" : tactic => withMainContext do
  let root ← Term.elabTerm root none
  let rules ← rules.getElems.mapM (elabRule ·)
  let claims ← claims.getElems.mapM (Term.elabType ·)
  let goal ← getMainGoal
  for simplify in #[false, true] do
    let context ← prepareInspectionContext root { hypotheses := rules, simplify }
    if context.truncated || context.contradiction?.isSome then throwError "unexpected status"
    assertProofs context claims
  if ← goal.isAssigned then throwError "inspection solved the user's goal"

elab "check_normalization " "[" facts:term,* "]" " using " "[" rules:term,* "]"
    " proves " "[" claims:term,* "]" : tactic => withMainContext do
  let facts ← facts.getElems.mapM (Term.elabTerm · none)
  let rules ← rules.getElems.mapM (Term.elabTerm · none)
  let claims ← claims.getElems.mapM (Term.elabType ·)
  let goal ← getMainGoal
  let (proofs, truncated) ← forwardInspectionProofs facts rules true 32 20_000
  if truncated then throwError "unexpected normalization cutoff"
  assertProofs {
    root := mkConst ``True.intro, scope := ← getLCtx
    localInstances := ← getLocalInstances, proofs } claims
  if ← goal.isAssigned then throwError "normalization solved the user's goal"

-- One Aesop run handles the complete chain, without calling Spytial's structural preparation.
example (P Q R : Nat → Prop) (S : Prop) (a : Nat) (hp : P a)
    (witness : ∀ n, P n → ∃ w, Q w ∧ R w)
    (finish : ∀ w, Q w → R w → S) : True := by
  check_normalization [hp] using [witness, finish] proves [S]
  trivial

-- Dependent choices, including fresh universe levels, are discharged into the original scope.
example (α : Type u) (β : α → Type v) (P : (a : α) → β a → Prop)
    (h : ∃ a, ∃ b, P a b) : True := by
  check_normalization [h] using [] proves
    [P (Classical.choose h) (Classical.choose (Classical.choose_spec h))]
  trivial

-- Plain `saturate` cannot bridge this chain; Aesop's normalizer also runs Lean's simplifier.
example (P Q S : Prop) (hp : P) (produce : P → ¬¬Q) (finish : Q → S) : True := by
  check_normalization [hp] using [produce, finish] proves [S]
  trivial

example (P Q S : Prop) (h : P ↔ Q) (finish : (P → Q) → S) : True := by
  check_normalization [h] using [finish] proves [S]
  trivial

-- Display decomposition must not erase premises needed by a supplied forward rule.
example (P Q S : Prop) (h : P ∧ Q) (finish : (P ∧ Q) → S) : True := by
  check_preparation h using [finish] proves [P, Q, S]
  trivial

example (P : Nat → Prop) (S : Prop) (h : ∃ x, P x) (finish : (∃ x, P x) → S) : True := by
  check_preparation h using [finish] proves [P (Classical.choose h), S]
  trivial

-- Non-Prop instances are typing data, even when the selected subject is a single proof.
example (α : Type) [Inhabited α] (P Q : α → Prop) (x : α) (h : P x)
    (rule : ∀ [Inhabited α] (x : α), P x → Q x) : True := by
  check_preparation h using [rule] proves [Q x]
  trivial

elab "check_derived_witness " root:term " using " rule:term : tactic => withMainContext do
  let root ← Term.elabTerm root none
  let rule ← Term.elabTerm rule none
  for simplify in #[false, true] do
    let context ← prepareInspectionContext root { hypotheses := #[rule], simplify }
    unless context.witnesses.size == 1 && context.proofs.size == 3 do
      throwError "derived witness was duplicated: {context.witnesses.size} witnesses, \
        {context.proofs.size} proofs"
    assertProofs context #[]

example (P Q R : Nat → Prop) (a : Nat) (hp : P a)
    (witness : ∀ n, P n → ∃ w, Q w ∧ R w) : True := by
  check_derived_witness hp using witness
  trivial

-- Multi-premise matching and chained applications export proofs of the advertised propositions.
example (P Q R : Nat → Prop) (a : Nat) (hp : P a)
    (pq : ∀ n, P n → Q n) (pqr : ∀ n, P n → Q n → R n) : True := by
  check_preparation a using [pq, pqr] proves [Q a, R a]
  trivial

-- A derived existential must be exposed before another selected rule can consume its body.
example (P Q R : Nat → Prop) (S : Prop) (a : Nat) (hp : P a)
    (witness : ∀ n, P n → ∃ w, Q w ∧ R w)
    (finish : ∀ w, Q w → R w → S) : True := by
  check_preparation a using [witness, finish] proves [S]
  trivial

-- Standard resolution exposes a branch, including a conjunction, without choosing an unknown one.
example (P Q R : Nat → Prop) (a : Nat) (h : P a ∨ (Q a ∧ R a)) (hn : ¬ P a) : True := by
  check_preparation a using [] proves [Q a, R a]
  trivial

elab "check_shared_witness " root:term : tactic => withMainContext do
  let root ← Term.elabTerm root none
  let context ← prepareInspectionContext root
  unless context.witnesses.size == 1 && context.proofs.size == 2 do
    throwError "unexpected witness decomposition"
  let witness := context.witnesses[0]!
  for proof in context.proofs do
    unless ((← inferType proof).find? (· == witness)).isSome do
      throwError "witness identity was not shared"
  assertProofs context #[]

example (R : Nat → Nat → Prop) (a b : Nat) (h : ∃ w, R a w ∧ R w b) : True := by
  check_shared_witness h
  trivial

elab "check_no_synthetic_witness " root:term " using " "[" rules:term,* "]" : tactic =>
    withMainContext do
  let root ← Term.elabTerm root none
  let rules ← rules.getElems.mapM (Term.elabTerm · none)
  for simplify in #[false, true] do
    let context ← prepareInspectionContext root { hypotheses := rules, simplify }
    unless context.witnesses.isEmpty do throwError "allocated an unnecessary witness atom"
    for proof in context.proofs do
      let type ← whnf (← inferType proof)
      if type.isAppOf ``Nonempty then
        throwError "manufactured an inhabitation fact for the renderer"
      if (type.find? (·.isAppOf ``Classical.choose)).isSome then
        throwError "retained a duplicate anonymous witness"
    assertProofs context #[]

-- No displayed relation uses the vacuous binder, so inspection needs no witness atom.
example (α : Type) (P : Prop) (h : ∃ _ : α, P) : True := by
  check_no_synthetic_witness h using []
  trivial

-- A named witness whose body is already represented must not gain a duplicate unknown.
example (R : Nat → Nat → Prop) (a b : Nat) (known : R a b) (h : ∃ w, R a w) : True := by
  check_no_synthetic_witness a using []
  trivial

-- Reordering the same premises must not allocate a second, anonymous endpoint.
example (R : Nat → Nat → Prop) (a b : Nat) (h : ∃ w, R a w) (known : R a b) : True := by
  check_no_synthetic_witness a using []
  check_preparation a using [] proves [R a b]
  trivial

-- The named witness can be established by components of a later conjunction too.
example (R : Nat → Nat → Prop) (S : Nat → Prop) (a b : Nat)
    (h : ∃ w, R a w ∧ S w) (known : R a b ∧ S b) : True := by
  check_no_synthetic_witness a using []
  check_preparation a using [] proves [R a b, S b]
  trivial

-- A proof-focused inspection cannot reuse an ambient witness whose evidence was not admitted.
example (R : Nat → Nat → Prop) (a b : Nat) (h : ∃ w, R a w ∧ R w b)
    (named : Nat) (known : R a named ∧ R named b) : True := by
  check_shared_witness h
  trivial

-- Omitting duplicate derived witnesses must not discard an original premise about a choice.
example (R : Nat → Nat → Prop) (a b : Nat) (known : R a b) (h : ∃ w, R a w)
    (value : Classical.choose h = 7) : True := by
  check_preparation a using [] proves [Classical.choose h = 7]
  trivial

example (P : Nat → Prop) (R : Nat → Nat → Prop) (a b : Nat) (known : R a b)
    (hp : P a) (witness : ∀ n, P n → ∃ w, R n w) : True := by
  check_no_synthetic_witness a using [witness]
  trivial

elab "check_refuted_inspection " root:term : tactic => withMainContext do
  let root ← Term.elabTerm root none
  let context ← prepareInspectionContext root
  let some proof := context.contradiction? | throwError "missed a contradiction"
  discard <| checkInspectionProof (mkConst ``False) proof

-- Lean handles reflexive disequalities; Spytial does not implement its own contradiction matcher.
example (n : Nat) (h : n ≠ n) : True := by
  check_refuted_inspection h
  trivial

private inductive ImpossibleRelation : Nat → Prop

example (n : Nat) (h : ImpossibleRelation n) : True := by
  check_refuted_inspection h
  trivial

elab "check_bounds " root:term " using " rule:term : tactic => withMainContext do
  let root ← Term.elabTerm root none
  let rule ← Term.elabTerm rule none
  let zero ← prepareInspectionContext root { hypotheses := #[rule], maxSteps := 0 }
  unless zero.truncated do throwError "zero steps concealed pending inference"
  let bounded ← prepareInspectionContext root { hypotheses := #[rule], maxSteps := 1 }
  unless bounded.truncated do throwError "a generative rule appeared saturated"
  unless bounded.proofs.size > zero.proofs.size do throwError "lost the completed prefix"
  assertProofs bounded #[]
  let capped ← prepareInspectionContext root { hypotheses := #[rule], maxFacts := 1 }
  unless capped.truncated && capped.proofs.size == 1 do throwError "fact bound was not enforced"
  let timed ← prepareInspectionContext root { hypotheses := #[rule], maxHeartbeats := 0 }
  unless timed.truncated do throwError "missing budget status"
  assertProofs timed #[]

example (P : Nat → Prop) (h : P 0) (step : ∀ n, P n → P (n + 1)) : True := by
  check_bounds h using step
  trivial

elab "check_last_step " root:term " using " rule:term : tactic => withMainContext do
  let root ← Term.elabTerm root none
  let rule ← Term.elabTerm rule none
  let context ← prepareInspectionContext root { hypotheses := #[rule], maxSteps := 1 }
  if context.truncated then throwError "a completed last step was called truncated"
  assertProofs context #[← inferType (← mkAppM' rule #[root])]

example (P Q : Nat → Prop) (h : P 0) (step : P 0 → Q 0) : True := by
  check_last_step h using step
  trivial

elab "check_excluded_premise " root:term " using " rule:term
    " without " omittedName:ident : tactic =>
  withMainContext do
    let root ← Term.elabTerm root none
    let rule ← elabRule rule
    let omitted ← getFVarId omittedName
    let context ← prepareInspectionContext root {
      hypotheses := #[rule], excludedHypotheses := #[omitted] }
    if context.contradiction?.isSome then throwError "Aesop used an excluded premise"
    assertProofs context #[]

example (P : Nat → Prop) (h : P 0) (step : P 0 → False) : True := by
  check_excluded_premise (0 : Nat) using step without h
  trivial

-- Explicit exclusion also prevents an ambient data instance from instantiating a rule.
example (α : Type) [inst : Inhabited α] (P : α → Prop) (x : α) (h : P x)
    (reject : ∀ [Inhabited α], P x → False) : True := by
  check_excluded_premise h using reject without inst
  trivial

elab "check_proof_focus " root:term " using " rule:term : tactic => withMainContext do
  let root ← Term.elabTerm root none
  let rule ← elabRule rule
  let context ← prepareInspectionContext root { hypotheses := #[rule] }
  if context.contradiction?.isSome then throwError "proof inspection used an ambient premise"
  assertProofs context #[]

example (P Q : Prop) (hp : P) (hq : Q) (reject : Q → False) : True := by
  check_proof_focus hp using reject
  trivial

-- A Prop-valued instance is a premise, so it cannot leak into a focused proof inspection.
private class PropInstance (P : Prop) : Prop where
  proof : P

example (P Q : Prop) [PropInstance P] (hq : Q)
    (reject : ∀ [PropInstance P], Q → False) : True := by
  check_proof_focus hq using reject
  trivial

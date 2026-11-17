# Inspecting terms with evidence

Spytial inspects a Lean term at a particular program or proof location. It draws
the structure available by computation, then uses local proofs to expose further
structure or relations. The term may be a whole value, a symbolic function input,
a partially determined result, or a proof of an existential statement.

**Evidence is a Lean proof term `p : P` in the original local context `Γ`.**
There is no separate fact language: `inferType p` supplies `P`. For example:

- `p : xs = x :: tail` justifies refining a symbolic list to a cons cell;
- `p : edge a b` justifies a displayed edge;
- `p : height t = n + 1` justifies an observation result;
- `h : ∃ w, edge a w ∧ edge w b` supplies one shared term `Classical.choose h`
  and proofs of both edges involving that term.

Evidence does not enumerate the meaning of the context. Missing evidence leaves
a relation or value unknown. A witness term does not assert uniqueness or
distinctness from other atoms. Unresolved disjunctions cannot supply either
branch as an unconditional tuple.

## Preparation, inference, and interpretation

1. Collect permitted local proofs, or decompose the selected proof subject.
   `nvm` excludes a declaration as an evidence source for this inspection;
   `fyi` supplies additional proofs or forward rules. Exclusion takes precedence
   for the same bare local declaration. It does not retract assumptions from
   the user's theorem or invalidate other proofs that depend on them.
2. Use Lean's simplifier and eliminators to expose conjunctions, equivalence
   directions, and shared existential witnesses. Simplification is enabled at
   the user-facing inspection entry points. Named applications keep the
   vocabulary of their proof types for display.
3. Run Aesop's normalization engine once, with selected forward rules and Lean's
   simplifier. Standard conjunction eliminators, `Iff.mp`/`Iff.mpr`,
   `Classical.choose_spec`, and `Or.resolve_left`/`Or.resolve_right` participate
   in that same engine. Aesop exposes a derived existential, feeds its body to
   subsequent rules, and simplifies intermediate conclusions. Spytial does not
   schedule those steps or restart inference after each conclusion. The engine
   matches admitted proof premises; it does not enumerate arbitrary values to
   instantiate universal statements.
4. Export derived proofs from the temporary proof state and check them in the
   original scope. A hypothesis introduced by automation is not itself evidence
   in the original scope until its derivation has been discharged.
5. Select the proofs relevant to the values actually represented by the root,
   then decode supported propositions as relations and equalities as refinements.
6. Evaluate requested observations. Particular residual expressions can generate
   focused `simp`/`omega` queries; predicate observations use retained evidence
   and bounded constructor search. Successful answers carry checked proofs.

Steps 1–4 are an adapter around existing Lean operations and Aesop. The matcher,
rule indexing, and forward application are Aesop's. Selection, observation
questions, relation decoding, and visualization belong to Spytial.

`InspectionContext` stores the inspected term, original scope and local instances,
proof terms, witness terms, and operational status. The scope interprets terms;
it does not automatically authorize every ambient proposition as a search premise.
The temporary forward context exposes only admitted proofs to Aesop matching.
The record is an internal integration object, not an unforgeable theorem type.
The checking boundary is `checkInspectionProof`.

## Bounds and state

Preparation uses Aesop's default normalization budget (currently 100 successful
steps), caps admission at 128 propositions, and has one heartbeat budget for the
normalization call.
A step can apply a forward rule to multiple matches or simplify hypotheses.
These steps replace the former adapter batches; they are not proof depth.
Definitionally equal conclusions are omitted, including choice bodies whose
proof arguments differ. When an existential already has a represented named
witness, additional anonymous choice occurrences are omitted; no equality
between those witnesses is asserted.

A passive checkpoint in Aesop's step sequence records the current context and
Lean state. One extra step detects pending work at the limit; if it succeeds,
the adapter restores the last allowed checkpoint and reports truncation. A
quiescent last step is not called truncated. Heartbeat exhaustion also restores
the last checkpoint, and admission beyond the proposition cap reports
truncation. The checkpoint neither chooses nor applies rules. None of these
statuses claims logical completeness.

A proof returned by Lean's `contradiction` operation prevents an ordinary diagram.
Absence of a detected contradiction does not establish consistency. This includes
Lean's standard checks for reflexive disequalities and impossible inductive
premises. The contradiction is checked before
root projection; an unwanted contradictory source must be explicitly excluded.

Preparation and proof queries restore their temporary metavariable state. Exported
proofs contain no unresolved metavariables. Shared choice terms stay in the
original scope, so temporary witness variables cannot escape into an inspection.

## Functions, theorems, and whole values

Function and theorem inspections use the same pipeline. A function branch can
have constructor information, local definitions, and match equations, just as
a tactic state can have hypotheses and derived equalities. For example, a named
match equation `h : t = Tree.node l x r` supplies exactly the evidence needed to
draw those children of `t`.

The expression form of `spytial` preserves the program expression; inspection
does not compute a replacement value or add assumptions. The theorem explorer
records inspections produced at proof locations using this same context path.

Whole-value commands use the existing structural walker and computation path.
They need no fabricated proof context or saturation pass. Definition reduction
already exposes constructors and fields. Observation equalities and checked
reification retain their existing proof obligations where applicable.

## Ownership

- `SpytialLean/Context.lean`: structural preparation, scope, admission, and budgets.
- `SpytialLean/Context/Forward.lean`: Aesop normalization invocation, budget
  checkpoints, and original-scope proof export.
- `SpytialLean/Evidence.lean`: premise isolation, proof checking, and calls to Lean's
  contradiction and arithmetic tactics.
- `SpytialLean/InContext.lean`: relevance, contextual refinement, and relation decoding.
- `SpytialLean/LeanSelector.lean` and `PredicateObservation.lean`: evidence lookup,
  simplification, and predicate observations over represented terms.

The semantic model is in `SpytialLeanInspectionSemantics/Context.lean` and the
existing inspection formalization. Soundness assumes the retained propositions
hold and proves properties of their interpretation. It does not formalize or
claim completeness of the Aesop adapter. Regression tests check the runtime
integration, including proof export, witness sharing, exclusion, and boundedness.

## Why the adapter remains

Each remaining responsibility serves an inspection operation:

| Spytial requirement | Adapter responsibility | Delegated operation |
| --- | --- | --- |
| `fyi`, `nvm`, and inspecting one proof | Admit only the permitted premises and preserve their original scope | Lean local contexts and assertions |
| Shared, labelled unknowns and structural refinements | Expose conjunctions and existential bodies; reuse a named witness whose body is already represented | Lean eliminators, `Classical.choose`, and `simp` |
| A derived existential followed by another rule | Register standard Lean eliminators as forward rules | Aesop normalization, matching, indexing, and chaining |
| Evidence usable after automation returns | Close a temporary goal for each result and check the exported proof | Lean metavariable substitution and kernel checking |
| Responsive inspection and honest limit warnings | Cap admitted evidence; retain a checkpoint and probe at the step boundary | Lean heartbeats and Aesop's normalization driver |
| No ordinary diagram from contradictory premises | Ask for a proof of `False` using only admitted premises | Lean `contradiction` |
| A symbolic observation blocked on an ordering | Form the specific proposition needed by that observation | Existing selector simplification and Lean `omega` |

There is no Spytial inference loop, disjunction scheduler, contradiction matcher, or witness
inhabitation calculus. Vacuous binders introduce no display atoms or synthetic
`Nonempty` facts. The adapter does not reconstruct an existential certificate or
maintain a general-purpose logical snapshot. Its result is the finite input to
one inspection, not a promise to retain every kind of consequence of the context.

## Why normalization rather than just `saturate`?

Existential decomposition does **not** require a Spytial orchestration loop.
With `Classical.choose_spec`, `And.left`, and `And.right` registered as forward
rules, one Aesop saturation call handles:

```text
P a → ∃ w, Q w ∧ R w
Q w → R w → S
```

Ordinary `saturate` does not run `simp` between applications. For example,
`P → ¬¬Q` followed by `Q → S` needs the intermediate double negation simplified.
Spytial uses Aesop's existing normalization driver, which handles that
alternation too. Direct adapter tests exercise both examples without calling
Spytial's structural preparation, and check nested dependent choices in the
original scope. The structural traversal before and after automation serves
presentation: selecting leaf propositions and retaining shared witness labels.

The integration uses the normalization API in the pinned Aesop dependency,
including its stateful forward engine. It is an internal API, so dependency
upgrades must run the adapter and downstream smoke tests.

## Relation to lemma synthesis

Brendel, Sivaraman, and Millstein's *Synthesizing Implication Lemmas for
Interactive Theorem Proving* (`dilemma`, OOPSLA 2025) synthesizes intermediate
propositions and proposes implication lemmas connecting assumptions to a goal
([paper, §2.2](https://web.cs.ucla.edu/~todd/research/oopsla25b.pdf)). Its
counterexample filtering helps select candidates; a candidate becomes evidence
for Spytial only after Lean proves it. `dilemma` is relevant to discovering useful
lemmas, while Aesop supplies the existing machinery for chaining supplied,
proved rules. Spytial needs neither a lemma synthesizer nor its own inference
engine to interpret the resulting proofs as diagrams.

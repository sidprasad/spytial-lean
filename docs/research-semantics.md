# Relational inspection by computation and proof

Status: paper and formalization plan, 3 September 2026.

## 1. Central claim

> A value can be inspected using knowledge obtained either by computation or by proof.

The paper studies two ways to obtain a relational instance for a Lean term `e`:

```text
                    computation
               e ----------------> relational instance
               |
               | proof context
               v
          (Gamma, e) ------------> partial relational instance
```

Both results have the same relational interface. Spytial consumes that interface
without needing to know how its atoms and tuples were obtained.

The paper is therefore not a new semantics of diagrams. Spytial already supplies
the spatial semantics, specification language, and renderer. The new contribution
ends at the relational instance.

## 2. Paper shape

The argument has four parts.

### Part I: two sources of knowledge

In ordinary program inspection, Lean computes a value and its constructor structure
becomes relational data. In a proof, the selected term may not be computable, but
the local context can establish useful structure and relationships around it.

### Part II: one relational semantics

Computed and proof-derived inspection both produce typed relational instances.
Computed instances can be complete for their structural vocabulary. Proof-derived
instances contain finite positive knowledge and have an open-world interpretation:
an absent tuple is unknown, not false.

### Part III: metatheory

We relate each producer to the meaning of its relational output:

- computational adequacy;
- soundness of proof-derived tuples;
- preservation of shared existential witnesses;
- the open-world interpretation of missing tuples; and
- agreement of the structural fragments when the context determines a concrete
  value.

### Part IV: payoff

Because the outputs share one interface, the same Spytial specification can
visualize a concrete value, a partially computed value, and a value known only
through proofs. A new domain requires no custom widget renderer.

## 3. The semantic boundary

The complete pipeline is:

```text
Lean term + optional local context
                 |
                 | computation and proof
                 v
      typed partial relational instance       new paper
                 |
                 | existing Spytial specification
                 v
             spatial diagram                  PLDI 2026
```

The following are downstream presentation choices and do not belong in the new
soundness theorem:

- box positions and spatial constraints;
- colors, labels, icons, and hidden fields;
- selection and visual emphasis; and
- user-defined atom merging used only for presentation.

In particular, a `SpytialIdentity` classifier can merge two displayed occurrences
without proving the represented Lean terms equal. Semantic soundness must be stated
for a pre-presentation instance, or be explicitly restricted to proof-producing
identity policies.

## 4. Inputs

Assume an implicit Lean environment `Sigma` containing definitions and inductive
declarations. Inspection receives:

- a well-formed local context `Gamma`;
- a term `e` with `Gamma |- e : tau`;
- a finite set `O` of unary observations; and
- finite extraction and normalization budgets `B`.

Command mode uses an empty local context. Tactic mode uses the current proof
context. Both modes share `Sigma`, so both may compute with Lean definitions.

The Spytial spatial specification is not an input to extraction. It is applied to
the resulting instance.

## 5. Relational instances

Let a semantic relation symbol carry an arity and Lean argument types. In the
current wire format this symbol is reconstructed from a relation name and a
tuple's type vector; it is not just the relation name. A finite instance
contains:

```text
D ::= <A, R, den, origin, status>

A       finite typed atoms
R       finite positive relation tuples over A
den     represented Lean term for each semantic atom
origin  semantic provenance for each atom or tuple
status  complete | partial | truncated
```

An origin is one of:

```text
structural(e, C, i)       field i of a constructor-headed residual of e
proved(phi, p)            decoded from a retained fact with p : phi
observed(f, t, r, p)      graph tuple justified by p : f t = r
```

Generated names and geometric positions are presentation metadata, not semantic
origins.

The production implementation now constructs an internal `TracedDataInstance`
that associates every emitted tuple with one of these origins; `ContextView`
retains that trace. Erasing it yields exactly the existing `JsonDataInstance`, so
the wire format sent to Spytial does not change.

Tuple-local column types are authoritative. `JsonRelation.types` is only
presentation/default metadata in the current format because reused field names
and generated `scrutinee` relations may contain heterogeneous tuples. The
effective serialized relation key is therefore `(name, tuple-type labels)`. The
labels are still not semantic types: aliases such as `Set Q` and their reduced
forms such as `Q → Prop` can label the same Lean type differently. A future wire
format could namespace relations, but semantic typing must retain Lean type
expressions and use definitional equality rather than string equality.

## 6. Incomplete-instance semantics

A proof-derived instance does not describe one fully known value. It describes
facts common to the possible worlds admitted by the context.

Following the existing IYKYK metatheory, let:

```text
Gamma : World -> Prop
```

select the worlds compatible with the local assumptions. A symbolic atom denotes
a value in each compatible world. A shared existential witness is one such
world-indexed value used by every tuple descended from that existential.

For a partial relational instance `D`, define:

```text
completions(Gamma, D) =
  { G(world) | Gamma(world) and every positive tuple of D holds in G(world) }
```

Equivalently, write:

```text
D <= G
```

when the ground instance `G` completes `D`: there is a type-respecting
interpretation of `D`'s symbolic atoms that preserves every positive tuple.
Additional atoms and tuples are permitted.

This is an open-world order. If `D <= G`, then adding an unreported tuple to `G`
does not make it cease to be a completion.

### Absence is not negation

For an open relation in a proof-derived instance:

```text
t not-in D(R)
```

does not imply:

```text
Gamma |- not R(t)
```

This is not a completeness failure of the diagrammer. It is the intended meaning
of a finite positive account of a proof context.

There are at least three reasons a true tuple can be absent:

1. no implemented rule derives it;
2. a finite budget stops extraction; or
3. root-focused projection removes it.

### Where closed-world reasoning is available

A fully evaluated algebraic value can enumerate all of its constructor fields over
the reachable value. Those structural relations may be treated as complete for
that value. This does not make every relation in a mixed instance closed:

- context relations remain open;
- an observer's graph is only enumerated over the frozen active domain; and
- unsupported or budget-limited observations remain partial.

The first formal model should therefore keep a complete computed structural
instance separate from an open proof-derived extension. A general system of
per-relation or per-domain closure annotations can wait.

## 7. Producer one: computation

Write:

```text
e ==> v
```

for Lean evaluation or definitional reduction to a value or residual `v`.
Computational relationalization walks the available constructor structure:

```text
relComp(e, O, B) = structuralRel(v) union observedRel(v, O, B)
```

For a constructor-headed residual:

```text
e ==> C(t1, ..., tn)
```

relationalization introduces an atom for `e`, recursively relationalizes every
data field, and adds the corresponding field tuples. Types and proof fields may be
omitted according to the declared data mode.

If reduction is stuck, the residual receives one opaque semantic atom. This atom
is not an assigned Lean metavariable and does not assert a concrete value.

### Observations

For every requested unary function `f : alpha -> beta`, first freeze the represented
active domain. For each applicable `t`, residualization produces:

```text
Gamma ; B |- f t ==> r by p
Gamma |- p : f t = r
```

The instance adds the graph tuple `f(t, r)` and relationalizes the result `r`.
Freezing the domain prevents observations from recursively applying to the values
they introduce.

## 8. Producer two: proof

IYKYK extracts finite knowledge about the selected root:

```text
know_B(Gamma, e) = inconsistent(p) | afaik(K)
```

where `K` contains:

- a root;
- stable witness terms;
- proposition/proof pairs; and
- an explicit truncation flag.

Each fact `(phi, p)` satisfies:

```text
Gamma |- p : phi
```

Root-focused projection selects the certified component relevant to the values
represented by `e`. A partial decoder maps supported propositions to relation
tuples:

```text
decode(phi) = tuples
```

Unsupported propositions contribute no tuples. The decoder does not invent an
approximate interpretation.

Proof-derived relationalization is:

```text
relProof(Gamma, e, O, B) =
  match know_B(Gamma, e) with
  | inconsistent(p) => inconsistent(p)
  | afaik(K) =>
      structuralRel(refine(e, K))
      union decode(project_e(K))
      union observedRel(project_e(K), O, B)
```

An established equality `e = v` may expose the structure of `v` while preserving
`e` as the selected root. Cycles among equalities must remain finite and fall back
to an opaque atom.

An inconsistent context is a separate result. Explosion would permit any tuple,
so constructing an ordinary instance would be sound in the least useful possible
sense.

## 9. The metatheorems we want

### 9.1 Computational adequacy

If a closed term evaluates to a value and the walk does not exhaust its budget:

```text
e ==> v
------------------------------
relComp(e, O, B) ~= relValue(v, O)
```

The equivalence is typed relational isomorphism, ignoring generated atom IDs and
tuple order.

### 9.2 Proof-instance soundness

Every context-compatible world completes the proof-derived instance:

```text
relProof(Gamma, e, O, B) = D
rho |= Gamma
--------------------------------
D <= ground(rho, e, O)
```

`ground` must include the relevant relational neighborhood, not merely the
constructor fields reachable from the root, because context facts can relate `e`
to other values.

An equivalent tuple-level statement is that every `proved(phi, p)` origin has a
kernel-checked `p : phi`, and every `observed(f, t, r, p)` origin has a
kernel-checked `p : f t = r`.

### 9.3 Open-world interpretation

The denotation of a partial instance is its upward-closed set of completions:

```text
D <= G and G subset-of G'
--------------------------
          D <= G'
```

Therefore tuple absence in `D` carries no negative meaning. A small countermodel
can demonstrate two completions of the same `D` that disagree on an absent tuple.

### 9.4 Witness coherence

All tuples descended from one extracted existential use the same symbolic atom.
Under every completion, those occurrences receive one value.

This is stronger and more relevant than merely giving the occurrences the same
display label.

### 9.5 Structural agreement

Full equality between computed and proof-derived instances is usually too strong:
the proof context may contribute additional relations that computation alone does
not enumerate.

The useful theorem restricts both instances to the structural vocabulary. If the
context determines `e` to equal a closed value `v`, extraction finds that equality,
and the structural walk terminates:

```text
Gamma |- e = v
------------------------------------------
struct(relProof(Gamma, e, O, B))
  ~= struct(relComp(v, O, B))
```

A weaker theorem, requiring less extractor completeness, states that the computed
instance is a completion of the proof-derived structural fragment.

### 9.6 Projection and truncation preserve soundness

Deleting facts or stopping after a certified prefix cannot make any remaining tuple
unsound. These properties already exist for IYKYK knowledge; they must be lifted
through relational decoding.

## 10. The payoff through Spytial

The payoff statement is:

> Because computation and proof produce the same relational interface, the same
> Spytial specification can visualize a concrete value, a partially computed value,
> and a value known only through proofs, without a domain-specific renderer.

Spytial contributes exactly the downstream properties we need:

- selectors range over relational data rather than host-language syntax;
- specifications are independent of how tuples were obtained;
- constraints and directives compose without changing extraction;
- symbolic atoms and extra relations use the ordinary diagram pipeline; and
- existing inconsistency handling concerns the spatial specification, independently
  of proof-context inconsistency.

The lightweight-integration claim is empirical. For each case study, report:

- Spytial specification size;
- any domain adapter or custom relationalizer code;
- changes required to the existing proofs;
- code shared between command and tactic inspection; and
- absence of domain-specific widget or rendering code.

## 11. Three case studies

Each domain uses one relational vocabulary and one Spytial specification in three
states:

```text
computed value | partial program value | proof-constrained value
```

### AVL rotation

Stresses recursive structure, unknown subtrees, key-order relationships, numeric
height observations, and equality refinement during a rotation proof.

### Heap or abstract-machine state

Stresses aliasing, shared existential locations, environments, stores, and a
transition justified by operational semantics or a Hoare-style proof.

### Automaton or transition system

Stresses cyclic structure, reachability, sets of possible states, and relational
facts not reducible to constructor fields.

Union-find and insertion sort can remain supporting examples, but the headline
three should make it difficult to characterize the system as tree visualization.

For each domain, evaluate:

1. whether exactly the same spatial specification is reused;
2. which tuples arise from structure, retained proofs, and observations;
3. how many desired facts are represented or remain unsupported;
4. whether symbolic identities and evidence survive translation;
5. integration and specification size; and
6. extraction, observation, and rendering latency.

This supports claims about semantics, expressiveness, reuse, and integration cost.
It does not claim improved human comprehension without a user study.

## 12. What is already formalized

The existing work is a substantial starting point, but it ends before relational
instances.

### IYKYK abstract metatheory

`metatheory/IykykMetatheory.lean` already defines possible-world contexts,
entailment, finite knowledge, and knowledge soundness. It proves:

- soundness of the implemented logical rule shapes;
- sound and lossless decomposition of conjunctions, equivalences, and nested
  existentials;
- preservation of one shared witness across existential descendants;
- counterexamples for unrelated witnesses and arbitrary disjunction choice;
- sound fact admission into certified knowledge;
- preservation of soundness by projection and truncation;
- preservation under context strengthening; and
- the semantic reason to separate inconsistent contexts.

### IYKYK runtime certification

The runtime `Afaik` and `Inconsistency` constructors are private. Facts enter through
checked smart constructors. `Afaik.certificate` conjoins retained facts, abstracts
each shared witness once, and `Lean.Kernel.check` checks the combined claim in the
captured local context.

This gives strong dynamic assurance that the knowledge entering Spytial is
proof-backed.

### Spytial Lean implementation evidence

The current implementation already has:

- generic constructor relationalization;
- exact sharing of symbolic terms and extracted witnesses;
- equality-based structural refinement with cycle guards;
- translation of retained context facts into ordinary relation tuples;
- proof-producing observation residualization;
- a frozen observation domain;
- separate inconsistency and truncation status; and
- extensive canonical-output and proof-certificate tests.

These tests establish important executable behavior, but they are not a formal
relational semantics or a proof that the runtime implements one.

### Existing Spytial metatheory

The PLDI 2026 formalization begins from a relational instance and proves properties
of selectors, spatial constraints, realizations, program composition, and spatial
refinement. It does not formalize how host-language computation or a proof context
produces that starting instance.

That missing producer boundary is the natural scope of the new formalization.

## 13. What is missing

### Gap A: a typed partial relational model

There is now a first wire-level definition in
`metatheory/SpytialLeanMetatheory/RelationalInstance.lean`. It defines atom and
tuple membership, label-preserving `WireHom`/`WireCompletes` laws, exact
trace-origin coverage, and an executable counterexample showing that an absent
tuple is unknown. Crucially, it operates on the actual
`SpytialLean.JsonDataInstance` returned by production. Membership uses
tuple-local labels, matching the heterogeneous generated relations that occur in
production.

This is not yet the typed semantic model. Still missing are:

- relational signatures and typed atoms;
- positive partial instances;
- symbolic or witness atoms;
- ground instances;
- completion `D <= G`; or
- relational isomorphism up to atom renaming.

Raw JSON also omits the Lean denotation of each atom and the origin of each
tuple. Consequently, the current homomorphism is only a wire-level
positive-information order. Those meanings are required before the
computation/proof bridge can be stated honestly.

### Gap B: a semantics for fact decoding

IYKYK proves that a proposition is true, but Spytial then turns its expression into
atoms and tuples. We have not formalized what each emitted tuple means or proved
that decoding a supported proposition preserves its meaning.

This is the most important missing soundness link.

The implementation now records each successful decoding as a `proved` tuple
origin containing the exact displayed proposition, IYKYK proof, and
column-aligned arguments. The proof-context producer defensively rechecks the
proof and reruns the decoder before returning the trace; IYKYK's sealed `Afaik`
and final certificate remain the source of proof validity. What remains here is
the abstract interpretation of that decoder and its possible-world soundness
theorem.

The first decoder theorem should cover only:

- relation applications `R t1 ... tn`;
- named function graph equations `f t1 ... tn = r`.

IYKYK already owns conjunction and existential decomposition, including shared
witnesses. Equality-based structural refinement belongs in the later bridge
theorem. Re-formalizing either inside the decoder would blur the package
boundary. Other atomic propositions may remain unsupported.

### Gap C: computational relationalization

The current generic walker is tested, including differential testing against a
reference implementation, but has no abstract value language or adequacy theorem.

We need a small algebraic value language with constructors, opaque terms, and named
fields, plus a pure relationalization function. Prove that reduction followed by
relationalization agrees with relationalizing the resulting value.

Formalizing arbitrary `Lean.Expr`, typeclass-driven identity, or custom
relationalizers is unnecessary for the first paper model.

### Gap D: the bridge theorem

Nothing currently connects:

```text
Gamma |- e = v
```

to agreement between proof-derived and computed structural instances. The theorem
needs explicit assumptions about equality discovery, termination, observations,
and the vocabulary being compared.

We should not state unconditional equality between the full instances: contextual
facts can legitimately add more tuples.

### Gap E: observation lifting

Runtime observations retain checked equalities, and tests kernel-check those
equalities. Missing from the abstract model are:

- the frozen active domain;
- graph-tuple construction from `f t = r`;
- composition of successive normalizations; and
- the theorem that every observation tuple is valid in every compatible world.

### Gap F: executable correspondence

The IYKYK metatheory-to-runtime connection is structural and dynamically certified.
The new runtime-correspondence module establishes exact but deliberately small
facts about the actual implementation: `WalkState.toDataInstance` preserves the
accumulated atoms, and both `relationalize` and `relationalizeAfaik` are their
evidence-producing walks followed by evidence erasure. Thus the computation and
proof-context producer entry points are both in scope.

These erasure theorems are definitionally true by construction. That is useful
architecture, not semantic correctness: it ensures that a checker is attached
to the producer whose output users see. Canonical and differential tests provide
backward-compatibility evidence, while origin-specific soundness theorems must
still justify what the tuples mean.

The production walkers now also retain a per-tuple origin classified as
structural, symbolic, proved, observed, tabulated, synthetic, or custom. A proved
origin carries the exact proposition and proof obtained from IYKYK, while the
legacy custom-relationalizer API is conservatively marked custom. Both producers'
existing APIs are exact erasures of these traces.

What remains missing is semantic validation: an origin tag is not itself a
semantic certificate. The structural trace checker proves exact correspondence
between output tuples and origins and rejects malformed arities or dangling atom
references. The `proved` case additionally checks evidence, decoder agreement,
column labels, and term alignment. The Spytial translation still needs an atom
interpretation using Lean types and a semantic correspondence theorem.

There were two viable endpoints:

1. implement a pure reference producer and prove it correct, then differentially
   test the `MetaM` implementation against it; or
2. enrich the internal view with per-tuple origins and run a small checker that
   validates the semantic instance before erasing evidence for JSON.

The implementation now follows the second route incrementally. The checker
currently establishes exact trace/output correspondence and validates the
`proved` decoding seam. The next checkpoint gives accepted atoms and relations
a semantic interpretation and proves that validator sound. `custom` remains
outside the generic theorem.

### Gap G: closure boundaries

The slogan "computed instances are closed; proof instances are open" is too coarse.
Closure may apply only to constructor fields reachable from a computed root, while
context relations and bounded observations remain open.

The first model should prove completeness only for computed structural relations
and give all proof-derived positive relations an open-world meaning. A more general
closure annotation system is optional future work.

## 14. Minimum viable formalization

The minimum credible mechanization is smaller than the runtime system.

### Module 1: relational instances

Define:

```text
Signature
GroundInstance
PartialInstance
Completes
Isomorphic
```

Prove basic completion properties and the open-world countermodel for absence.

Status: the wire-level version over the production JSON type now compiles. Typed
signatures, well-formedness, denotations, ground instances, and isomorphism remain.

### Module 2: proof-derived instances

Reuse the possible-world setup and existential decomposition from IYKYK. Refine the
atomic formula case so atoms carry relational symbols and arguments. Define the
partial decoder and prove that every compatible world completes its output.

### Module 3: computed values

Define a typed algebraic value/term calculus with constructors and opaque terms.
Define `relValue` and `relComp`. Prove computational adequacy and completeness of
the structural fragment for closed values.

### Optional extension: observations

Add unary function graph observations with equality evidence and a finite frozen
domain. Prove observation-tuple soundness.

### Module 4: the bridge

State structural agreement under explicit hypotheses. Begin with the weaker
completion result; prove isomorphism only for the supported complete fragment.

## 15. Recommended order of work

1. Define semantic `Signature`, `PartialInstance`, `GroundInstance`, and
   `Completes` using Lean types rather than JSON strings.
2. Lift IYKYK's atomic facts into relational atoms and prove decoder soundness,
   open-world completion, and witness coherence.
3. Add the small computed-value calculus and prove structural adequacy.
4. Connect the already-instrumented production trace to these two semantics.
5. Derive structural agreement under an explicit discovered-equality hypothesis.
6. Add observations only after this core typechecks cleanly.

The repository already has the checked production trace and its exact JSON
erasure, plus a wire-level positive-information order. The next research
checkpoint should be steps 1-2. That is the shortest path to the paper's central
new theorem: a proof-backed tuple emitted by the real decoder holds in every
IYKYK-compatible world.

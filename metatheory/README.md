# Spytial Lean metatheory

This directory formalizes the producer boundary introduced by Spytial Lean:

```text
computation or proof context -> relational instance -> Spytial
```

The PLDI Spytial formalization begins at the relational instance and gives the
downstream spatial semantics. IYKYK formalizes and certifies finite knowledge
extracted from a proof context. This directory is intended to connect those two
boundaries.

The ownership boundary is deliberate:

- IYKYK owns extraction, shared witnesses, inconsistency, truncation, and the
  checked `(proposition, proof)` pairs in `Afaik`;
- Spytial Lean owns decoding those propositions into relation tuples, all
  computation-derived tuples, and the trace relating tuples to their origins;
- the metatheory interprets the trace and states the cross-boundary theorems.

## Runtime correspondence requirement

An abstract partial-instance calculus is not sufficient. The production
relationalizer must emit the object interpreted by the metatheory.

The production side therefore starts directly from
`SpytialLean.JsonDataInstance`, the actual type returned by `relationalize`.
`RelationalInstance.lean` gives that type a wire-level open-world order via
`WireHom` and `WireCompletes`. The semantic side is necessarily separate:
`SemanticInstance.lean` adds intrinsically typed tuples, a finite typed atom
domain, possible-world denotations, and ground relation interpretations. The
remaining bridge must show that a checked production trace realizes one of
those semantic instances; it may not posit a second, toy producer.

Typing is read from each `JsonTuple`, not from `JsonRelation.types`. The latter
is presentation/default metadata in the current wire format: reused field names
and generated `scrutinee` relations can legitimately contain tuples with
different column types. Thus the effective typed relation symbol is currently
`(name, tuple-type labels)`. Even those labels are not semantic types: a field
declared with the alias `Set Q` can point to an atom whose reduced type prints as
`Q → Prop`. The eventual typed semantics must retain Lean type expressions and
compare them by definitional equality. Both facts were exposed by running the
trace invariant against the real relationalizer.

`RuntimeCorrespondence.lean` imports the actual relationalizers and proves the
first exact implementation facts: `WalkState.toDataInstance` preserves the
walker's atom array, and both public producer entry points—`relationalize` for a
computed value and `relationalizeAfaik` for proof-context knowledge—are
definitionally their evidence-producing walks followed by evidence erasure. This
rules out a detached toy producer, while deliberately making no tuple-soundness
claim yet.

The erasure results are `rfl` by design. Their contribution is architectural:
the public API is factored through the traced producer, so a later soundness
checker applies to the object that production actually erases. They neither
prove that an origin is truthful nor establish backward compatibility with an
older commit; origin-specific theorems and canonical regression tests discharge
those separate obligations.

The production walker now constructs this internal traced instance:

```text
TracedInstance
  data      : JsonDataInstance
  emissions : [(relation, tuple, origin)]
  origin    : structural | symbolic | proved | observed
              | tabulated | synthetic | custom
```

Both computed-value and proof-context APIs expose their traced form. Their
established JSON/evidence APIs are definitionally the traced producer followed
by erasure. The executable structural checker additionally establishes that
output tuples and origins account for one another exactly, with aligned columns
and no dangling atom references. This remains a shape theorem, not semantic
soundness. The semantic checker can therefore treat origins separately:

- `structural`: justified by a constructor or projection rule;
- `symbolic`: records the Lean application represented by a function-graph
  tuple;
- `proved`: linked to the retained IYKYK proposition and proof;
- `observed`: linked to an equality proof `f t = r` or definitional reduction;
- `tabulated`: linked to the evaluated application or decided proposition;
- `synthetic`: given an explicit representation-only interpretation;
- `custom`: outside the generic soundness theorem unless the custom
  relationalizer supplies its own certificate.

The instrumented tuple-emission paths include constructor fields, structure
projections, symbolic function graphs, computed observations, finite function
tabulation, proposition tabulation, stuck-match `scrutinee` edges, retained
context facts, and custom relationalizers. Every ordinary production insertion
goes through the traced operation; the legacy `addTuple` API marks unrestricted
custom output as `custom`.

The proof-context producer already validates the tight `proved` slice at
runtime: it defensively rechecks the proof, reruns `propTupleShape?`, and checks
the relation name, decoded arguments, column labels, and alignment. Proof
validity fundamentally comes from IYKYK's sealed `Afaik` construction and final
certificate. `ProofDecoder.lean` now gives the semantic half of this boundary:
`ProofDecoding.sound` composes sound IYKYK knowledge with a decoder-reflection
certificate to prove completion, and `decodeAtomicFacts_sound` proves that
reflection by construction for semantic atomic relation facts. What remains is
the narrow reflection theorem showing that the production `Lean.Expr` decoder
realizes that atomic decoder.

## Tight theorem spine

The paper does not need one semantics for every implementation feature. Its
smallest convincing core has one common semantic instance and two producer
theorems:

1. **computed adequacy:** a terminating structural walk denotes the computed
   algebraic value;
2. **proof soundness:** every decoded proof-origin tuple holds in every world
   compatible with the IYKYK context; and
3. **runtime correspondence:** the real producers emit a checked trace whose
   erasure is exactly the instance consumed by Spytial.

Structural agreement when the context proves `e = v` should then be a corollary
of the first two results, not a third independent semantics. Observations,
synthetic relations, and certified custom relationalizers can extend this core
without obscuring it.

## Current semantic checkpoint

The first formal checkpoint consists of:

1. semantic atoms with intrinsically indexed types and contextual denotations;
2. completion and isomorphism for semantic instances;
3. a proof-to-tuple decoder with a possible-world soundness theorem; and
4. the bridge from checked production traces to that semantic model.

Items 1 and the completion half of item 2 are now formalized. In particular,
`completes_iff_tupleFacts` proves that semantic completion is exactly IYKYK
entailment of every emitted tuple. Item 3 is proved for an abstract certified
decoder and for atomic semantic relation facts. The shared-witness example
constructs two edges from one existential path and uses definitionally the same
contextual atom in both tuples.

The next load-bearing result is the remaining part of item 4: a realization of
the actual `TracedDataInstance` whose `proved` origins instantiate
`ProofDecoding`. That result must account for Lean expression typing,
definitional equality, atom reuse, and the output of `propTupleShape?`. These
belong to a small trusted reflection interface rather than a reimplementation
of Lean's type theory. After that bridge, the work proceeds to computed
structural adequacy, semantic isomorphism, and finally computation/proof
agreement.

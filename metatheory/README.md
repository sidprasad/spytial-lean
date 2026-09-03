# Spytial Lean metatheory

This directory studies one boundary:

```text
computed value or proof context -> relational instance -> Spytial
```

The PLDI Spytial work starts with a relational instance and explains how a
diagram is produced from it. This directory asks where that instance came
from, and what its tuples mean.

IYKYK and Spytial Lean have separate jobs:

- IYKYK extracts facts and shared witnesses from a Lean proof context. It
  retains a checked proof for every fact.
- Spytial Lean turns computed values and IYKYK facts into atoms and tuples. It
  records why each tuple was emitted.
- This metatheory connects those production records to typed mathematical
  relations.

## What “true” means here

A *world* is one assignment of values that satisfies the current Lean
hypotheses. A proof-derived atom may denote a different value in different
worlds. This is needed for an existential witness whose value is not fixed by
the context.

`Completes context data ground` says that every tuple in `data` is true in
every world allowed by `context`. It says nothing about a tuple that is absent
from `data`: an absent tuple is unspecified, not false.

## The production object

The metatheory is tied to `JsonDataInstance`, the type returned by the real
relationalizer. The walker first builds this internal object:

```text
TracedDataInstance
  data      : JsonDataInstance
  emissions : [(relation, tuple, origin)]

origin = structural | symbolic | proved | observed
       | tabulated | synthetic | custom
```

Erasing `emissions` gives exactly the JSON data consumed by Spytial. The
theorems in `RuntimeCorrespondence.lean` establish this by definition for both
`relationalize` and `relationalizeAfaik`.

The basic trace checker also establishes three concrete facts:

- every output tuple has at least one origin;
- every origin names a tuple that is actually in the output; and
- every tuple column names an output atom, with one type label per column.

These are shape facts. They do not, by themselves, say that a tuple is true.

## Actual Lean expressions and types

`LeanExprMeaning.lean` places real `Lean.Expr` values in the semantic model.
It does not replace Lean's kernel with a second type theory.

The interface records:

- which expression is a type;
- when a term has a type;
- Lean definitional equality for both terms and types;
- the value denoted by a checked term in each allowed world; and
- the proposition denoted by a checked proof claim.

Semantic types are quotients of actual Lean type expressions by definitional
equality. Thus an alias such as `Set Q` and its reduced form `Q → Prop` name
the same semantic type.

This interface is the trusted boundary. Lean's `inferType`, `isDefEq`, and
kernel proof check supply its runtime evidence. The metatheory assumes the
usual sound interpretation of those successful checks; it does not claim to
prove Lean's kernel sound inside Lean.

## Proof-derived tuples

The production proof checker now returns a sealed `CheckedProofTrace`
containing `CheckedProvedOrigin` values. For each `proved` origin it:

1. checks that the retained proof has the retained proposition as its type;
2. reruns the proposition-to-tuple decoder;
3. retains the actual predicate head and its hidden Lean parameters, rather
   than relying on a short display name;
4. checks the decoded arguments and their inferred Lean types; and
5. checks that each decoded term names the atom in the corresponding tuple
   column.

Keeping the predicate expression matters. Two distinct predicates can have
the same short name, and one predicate head can be used with different type or
type-class parameters.

`ProductionProofDecoder.lean` connects these checked values to the semantic
model. `ProductionProofRealization.toProofDecoding` proves that they instantiate
the common `ProofDecoding` interface once their Lean expressions have been
given their mathematical meanings. `ProductionProofRealization.sound` then
proves that every emitted proof-derived tuple is true in every world allowed
by sound IYKYK knowledge.

The only semantic premise specific to proposition decoding is
`proposition_implies_tuple`: whenever the proposition before decoding is true,
the typed tuple after decoding must be true in the same context-compatible
world. Soundness does not need the stronger claim that these two predicates
are equal.

## Computed structural tuples

The first computed theorem deliberately covers the direct structural fragment:
constructor fields and structure projections. It does not silently include
observations, synthetic representation edges, or unrestricted custom
relationalizers.

The production walker now produces a sealed `CheckedStructuralTrace` after
checking each actual `structural` origin. It checks
the source and child expressions, inferred Lean types, atom links, and whether
the origin is a real constructor field or a definitionally equal structure
projection. It also checks a concrete completeness property: every represented
constructor has a structural tuple for each non-proof, non-function data
field. Function fields use the separate tabulation rules.

`ComputedRelationalization.lean` composes these local facts. Given a semantic
interpretation of the checked origins, it proves both:

- **adequacy:** every emitted structural tuple is true; and
- **structural completeness:** every required first-order structural field is
  present.

These are the two directions meant by “the diagram represents the computed
value.”

## Comparing computation and proof

Fresh atom names and output order are presentation details, so equality of
JSON files is too strong. `SemanticIsomorphism.lean` defines agreement as a
type-preserving bijection of atoms that:

- preserves the value denoted by each atom; and
- maps every positive tuple in each direction.

It proves that semantic isomorphisms compose and preserve completion. It also
gives the intended computation/proof proof rule: if the computed instance and
the proof-derived instance are each isomorphic to one common reference
instance, they structurally agree with each other.

## Tight theorem spine

The smallest paper result is now organized around four claims:

1. actual Lean expressions, typing, and definitional equality have an explicit
   semantic interface;
2. a sealed proof trace produces `ProofDecoding` once proposition decoding is
   shown to preserve meaning;
3. a sealed direct-structural trace gives adequacy and completeness once its
   checked origins are interpreted; and
4. two outputs for the same reference value agree up to semantic atom
   renaming.

## What is still missing

The framework and composition theorems are checked. The following concrete
instances still have to be supplied before the main result is complete:

1. Construct the `LeanExprMeaning` interpretation for the captured local
   context and state its trusted-kernel assumptions precisely.
2. Prove `proposition_implies_tuple` for both cases of the production decoder:
   an atomic predicate and an equation decoded as a function-graph tuple.
3. Build the semantic `TraceRealization` automatically from a production
   trace, its provenance map, and selector evidence. This must prove that one
   atom ID denotes one shared semantic atom even when several Lean expressions
   name it.
4. Interpret the checked constructor-field and projection records and use the
   runtime coverage check to construct `ComputedStructuralCertificate`.
5. For each case study, define the common reference instance and prove the two
   semantic isomorphisms: computed-to-reference and proof-to-reference.

Those are now narrow proof obligations attached to the actual relationalizer.
They are not a request to formalize all of Lean or all optional Spytial
features.

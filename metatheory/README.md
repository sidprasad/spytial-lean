# Relational inspection by computation and proof

## The idea

A value can be inspected using knowledge obtained either by computation or by
proof.

Ordinary Spytial Lean evaluates a term as far as Lean permits and turns the
available value structure into relational data. In a theorem proof, evaluation
may stop before that structure is visible. The local context may nevertheless
prove what the selected term is or prove useful relations involving it.

The operation studied here is therefore:

```text
inspect(Gamma, e)
```

It produces positive relational data about `e` from two sources:

```text
computation -----------\
                        > structural data + proved facts -> Spytial
proof context ---------/
```

Both sources use one typed relational interface. Spytial does not need a
different specification or renderer for a computed value, a partial program,
or a value whose structure is known through a proof.

## Scope

This model ends at the relational instance.

- IYKYK finds proof-backed knowledge in a Lean context.
- Spytial Lean combines computed structure and decoded proof facts.
- Spytial consumes the resulting relations and produces a diagram.

Spytial already gives meaning to specifications, spatial constraints, and
diagrams. This development explains how Lean produces the relational input to
that system.

It is not a verification of Lean's kernel, evaluator, or metaprogramming
runtime. It also does not attempt to certify arbitrary custom relationalizers.

## The semantic model

`Semantic.lean` defines:

- typed relation symbols;
- typed heterogeneous tuples;
- finite positive relational data;
- possible-world interpretations of atoms and relations; and
- `Sound`, meaning that every reported tuple is true in every world compatible
  with the current context.

The word *positive* is important. If a tuple is missing, the model draws no
conclusion about it. The fact may be false, unavailable to the extractor, or
outside the current finite budget. Removing tuples therefore preserves
soundness, and combining two sound tuple sets preserves soundness.

## Proof-derived data

IYKYK already proves that every retained fact follows from the Lean context.
`Knowledge.lean` represents the supported relational subset of that knowledge.
Each decoded tuple points to its corresponding semantic fact in the IYKYK
knowledge value.

The theorem `DecodedKnowledge.sound` then proves:

```text
IYKYK knowledge is sound
each decoded tuple is one of its relational facts
-------------------------------------------------
every decoded tuple is true
```

The premise is not that the output tuple is true. It is the smaller interface
fact that the decoder selected a certified IYKYK fact. The concrete Lean
decoder checks the corresponding syntactic facts—the proof, relation, and
arguments—before returning a production trace.

## Structural data

The semantic model treats ordinary structural relationalization as an existing
component:

```text
StructuralRelationalizer.relationalize
StructuralRelationalizer.sound
```

This is the baseline on which proof-aware inspection builds. The new result
does not require a second structural relationalizer for proofs. Computation or
proof first resolves the selected expression to an available representation;
the same structural relationalizer handles that representation in both cases.

## What is proved

`Inspection.lean` proves four properties.

### 1. Resolution is independent of the knowledge source

A `ComputationResult` states that evaluation produces a value equal to the
selected expression. A `ProofResult` states that the context entails the same
kind of equality. Therefore, if computation and proof both resolve one
expression, their values agree in every compatible world.

### 2. Structural relationalization agrees

The main theorem is:

```text
computation_and_proof_have_same_relational_structure
```

In mathematical notation:

```text
Gamma |- e computes to v_c
Gamma |- e = v_p
---------------------------------------------
relationalize(v_c) = relationalize(v_p)
```

The equality is semantic. Production atom names are serialization details and
are not used to decide whether the values agree.

### 3. Proof inspection is a refinement

`Inspection.retains_ordinary_relationalization` proves that the full inspection
contains every atom and tuple in its ordinary structural part. Proof knowledge
may add facts, but it does not remove the computed structure.

### 4. The combined instance is sound

`Inspection.sound` combines the prior soundness of structural
relationalization with `DecodedKnowledge.sound`. Every tuple in the result is
therefore justified either by the ordinary relationalizer or by certified
IYKYK knowledge.

Together these results say:

```text
root(inspect(Gamma, e)) = relationalize(v)
inspect(Gamma, e)       = relationalize(v) + proved facts
Gamma                   entails every tuple in inspect(Gamma, e)
```

The combined theorem is
`Inspection.soundly_refines_computed_relationalization`. Given a computed
result and sound IYKYK knowledge, it proves all three statements at once.

## Why this matters for Spytial

`Presentation.lean` projects semantic relation symbols to the short relation
names used by Spytial. Each row retains its typed columns. Semantic relations
with the same short name therefore enter the same display namespace, while
remaining distinct semantic relations and retaining each row's schema.

`present_union` proves that projection preserves the structural-plus-proof
union exactly. `same_spytial_specification_for_computation_and_proof` proves
that any specification applied to the structural presentation receives the
same data whether computation or proof supplied the resolved value.

The practical consequence is:

> The same Spytial specification can display a concrete value, a partially
> computed value, and a proof-constrained value without a domain-specific
> renderer.

## Connection to the implementation

The production changes are deliberately smaller than the semantic model.

`TupleOrigin` records why the real relationalizer emitted each tuple. The
important cases are structural output and proof-backed output. Other existing
features retain distinct tags so that the core theorem does not silently claim
them.

Both production entry points have traced forms:

```text
relationalizeWithTrace
relationalizeAfaikWithTrace
```

Their existing public results are obtained by erasing the trace. No JSON or
renderer change is required. `RuntimeCorrespondence.lean` proves these erasure
equalities directly.

`ProductionTrace.lean` proves that a trace accepted by the executable checker
accounts for exactly the tuples in the erased production output. The
proof-context producer also rechecks each retained proof and reruns
`propTupleShape?` to confirm its relation and arguments.

This is an implementation connection, not an internal proof that Lean's kernel
is correct. Lean's kernel remains the trusted checker for Lean proof terms.

## Files

- `Semantic.lean`: typed positive instances and their possible-world soundness.
- `Knowledge.lean`: sound translation of certified IYKYK facts into tuples.
- `Inspection.lean`: computation/proof resolution, refinement, soundness, and
  the main agreement theorem.
- `Presentation.lean`: projection to named Spytial rows and specification reuse.
- `ProductionTrace.lean`: exact coverage of real JSON tuples by recorded origins.
- `RuntimeCorrespondence.lean`: exact erasure from traced producers to the
  existing public APIs.

## Deliberate boundaries

The current semantics covers ordinary structural relationalization and direct
proof-derived relations. The following can be handled independently:

- proof-producing observations;
- finite function tabulation;
- synthetic display edges; and
- certified custom relationalizers.

Unrestricted custom relationalizers remain outside the generic soundness claim.
Short JSON relation names are presentation identifiers; semantic relation
symbols remain distinct before projection.

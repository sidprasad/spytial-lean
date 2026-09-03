# Semantics of relational inspection

## Why Spytial in Lean is interesting

> A value can be inspected using knowledge obtained either by computation or
> by proof.

Lean presents the same program value in several situations. The value may be
fully evaluated. It may contain symbolic or stuck terms. It may occur inside a
proof, where the local context establishes facts that computation alone cannot
recover.

Spytial can treat all three situations through one relational interface:

```text
computed value       partial program       proof-constrained value
      |                     |                        |
      +------------- typed relational interface ----+
                            |
                  same Spytial specification
                            |
                         diagrams
```

“Same interface” means the same typed relational vocabulary. It does not mean
that every inspection contains the same tuples. A proof context may describe
only part of a value. It may also provide relations that ordinary computation
does not report.

A domain still needs a Spytial specification. It does not need a separate
renderer for each inspection situation. This is why the semantics matters:
the diagrammer remains independent of the source of the relational knowledge.

## What this formalization studies

We model relational inspection as a context-indexed operation:

```text
inspect(Gamma, e) = D
```

`Gamma` is the local Lean context. `e` is the term being inspected. `D` is a
typed, positive, partial relational instance.

Inspection uses two sources of knowledge:

```text
                         computation
                              \
              (Gamma, e) ---- inspect ----> D ----> Spytial
                              /
                   kernel-checked facts
```

Computation exposes constructor fields, structure projections, and reducible
applications. The proof context supplies checked facts about terms that may be
symbolic or only partly evaluated. Both sources contribute ordinary atoms and
tuples to `D`.

The implementation currently exposes these paths as `relationalize` and
`relationalizeAfaik`. The semantics treats them as cases of one inspection
operation. A fuller operation may also take requested observations and a
finite work limit. The first theorem excludes those extensions.

This distinction also explains the word *metatheory*. The semantics defines
what `inspect(Gamma, e)` means. The metatheory proves soundness, completeness,
and agreement properties of that semantics.

This work ends at the relational instance. Spytial already defines selectors,
spatial constraints, diagram refinement, layout, and rendering.

## Meaning of the relational instance

An inspection result contains positive information:

- an atom represents a typed Lean term;
- a tuple states that a typed relation holds of its atoms; and
- a tuple origin records why inspection emitted that tuple.

If a tuple is present, the producer must justify it. If a tuple is absent, no
conclusion follows. In particular, absence does not mean that the relation is
false.

The formal model follows IYKYK. A `World` is one interpretation of the free
terms in the local context. The predicate `context world` says that the
interpretation satisfies `Gamma`. The formulas below use `rho` for one such
world.

An atom obtained from a closed computed term has the same value in every
allowed world. A symbolic atom may have a different value in different worlds.
All uses of one extracted existential witness still denote one value within a
world.

`GroundInstance` interprets each typed relation symbol. The Lean proposition

```text
Completes context data ground
```

says that every tuple in `data` is true in every world that satisfies the
context. The code uses the name `Completes` because `ground` may contain more
information than the partial instance. In the paper, the direct statement is
that all emitted positive tuples are sound.

The following comparisons are useful:

- `rootStruct(D)` keeps the direct constructor-field and projection tuples
  belonging to the inspected root;
- `D1 <= D2` means that every tuple in `D1` is represented in `D2` by a typed,
  denotation-preserving atom map; and
- `D1 ~= D2` means that the two instances have the same typed relational
  structure after renaming generated atom identifiers and reordering tuples.

The exact Lean definitions may use different names. These are the paper-level
relations they must express.

## The final theorems

The work is directed at three headline results.

### 1. Inspection is sound

```text
D = inspect(Gamma, e)       rho satisfies Gamma
-------------------------------------------------
              every tuple in D is true in rho
```

This theorem covers every origin in the supported core. Structural tuples are
justified by computation. Proof-derived tuples are justified by checked facts
from `Gamma`.

This result is important for partial programs and proof-constrained values:
inspection may omit information, but it must not invent information.

### 2. Inspection agrees with ordinary relationalization on values

```text
v is a closed value
both walks finish under the same sound identity policy
------------------------------------------------------
rootStruct(inspect(empty, v)) ~= relationalize(v)
```

This is the conservativity result. Proof-aware inspection does not change the
meaning of ordinary Spytial relationalization when no proof information is
needed.

### 3. Proof refinement agrees with computation

The partial form is:

```text
Gamma proves e = v
inspection retains that equality
the identity policy does not merge unequal values
--------------------------------------------------
rootStruct(inspect(Gamma, e)) <= relationalize(v)
```

Even if inspection stops early, every reported structural tuple agrees with
the computed value.

The complete form adds successful field coverage:

```text
Gamma proves e = v
inspection retains that equality
the supported structural walk finishes
every supported field is emitted
the identity policy does not merge unequal values
--------------------------------------------------
rootStruct(inspect(Gamma, e)) ~= relationalize(v)
```

This is the main computation/proof bridge. It explains when a value known by
proof has the same structural description as a value known by computation.

The theorem compares `rootStruct(inspect(Gamma, e))`, not the full contextual
instance. The context may legitimately add predicates and relationships that
ordinary computation does not enumerate.

Two supporting results remain important:

- facts obtained from one existential statement reuse one semantic atom for
  their shared witness; and
- deleting tuples or stopping after a justified prefix preserves soundness.

## Scope of the first result

The first end-to-end result covers:

- direct constructor fields and structure projections;
- predicate applications and function-graph equations decoded from proofs;
- finite walks that do not exceed their work limit; and
- atom identity policies known to preserve the represented Lean value.

An unrestricted `SpytialIdentity` classifier may intentionally merge unequal
values for presentation. That merge can be useful in a diagram, but it is not
a semantic equality and is outside these theorems.

Bounded observations, tabulated functions, synthetic representation edges,
and custom relationalizers require separate soundness conditions. They should
not delay the first computation/proof result.

## Connection to the production relationalizer

The formalization uses the data produced by the real walker. Before it returns
ordinary JSON, the walker constructs:

```text
TracedDataInstance
  data      : JsonDataInstance
  emissions : [(relation, tuple, origin)]

origin = structural | symbolic | proved | observed
       | tabulated | synthetic | custom
```

Removing `emissions` gives the existing `JsonDataInstance` consumed by
Spytial. `RuntimeCorrespondence.lean` proves this by definition for the
computed and proof-aware entry points.

The general trace checker establishes that:

- every output tuple has an origin;
- every origin names an output tuple; and
- every tuple column names an output atom and has a type label.

These checks establish trace integrity. They do not establish that a tuple is
true.

For a proof origin, the production checker also:

1. checks the retained proof against its proposition;
2. runs the production proposition decoder again;
3. retains the actual predicate head and hidden parameters;
4. checks the decoded arguments and their inferred Lean types; and
5. checks that each decoded term names the recorded tuple atom.

For a structural origin, the production checker recognizes direct constructor
fields and structure projections. It checks their source terms, child terms,
types, and atom links. It also checks that every represented constructor has a
tuple for each supported first-order field.

The actual Lean expressions matter. JSON names such as `lt` are not unique
relation symbols. JSON type labels also do not account for definitional
equality. The semantic layer therefore retains relation heads, hidden
parameters, terms, and Lean type expressions.

## Results, files, and purpose

- **Positive JSON data.**
  [RelationalInstance.lean](SpytialLeanMetatheory/RelationalInstance.lean)
  proves tuple membership and trace coverage at the JSON boundary. This ties
  the account to the data sent to Spytial and shows that an omitted tuple need
  not be false.

- **Typed relational descriptions.**
  [SemanticInstance.lean](SpytialLeanMetatheory/SemanticInstance.lean) defines
  typed atoms, tuples, relation meanings, and partial-instance soundness. Its
  basic laws are proved. This gives computation and proof one semantic result
  type.

- **Meaning of Lean expressions.**
  [LeanExprMeaning.lean](SpytialLeanMetatheory/LeanExprMeaning.lean) defines the
  interface for actual Lean terms, types, and definitional equality. The
  production interpretation is still missing. This interface prevents JSON
  names and display strings from standing in for Lean semantics.

- **Abstract proof decoding.**
  [ProofDecoder.lean](SpytialLeanMetatheory/ProofDecoder.lean) proves soundness
  for an abstract proof-to-tuple decoder. This reuses IYKYK soundness instead
  of repeating its logic in Spytial Lean.

- **Production proof decoding.**
  [ProductionProofDecoder.lean](SpytialLeanMetatheory/ProductionProofDecoder.lean)
  connects checked production origins to typed tuples. The theorem is proved
  once a typed trace interpretation and `proposition_implies_tuple` are
  supplied. Constructing those values automatically remains open. This is the
  actual proposition-decoding boundary.

- **Computed structure.**
  [ComputedRelationalization.lean](SpytialLeanMetatheory/ComputedRelationalization.lean)
  proves conditional soundness and field coverage for computed structural
  tuples. Constructing its certificate from the production trace remains
  open. These two directions are needed for computed-value correctness.

- **Agreement up to atom names.**
  [SemanticIsomorphism.lean](SpytialLeanMetatheory/SemanticIsomorphism.lean)
  proves algebraic laws for typed, denotation-preserving atom maps and
  isomorphisms. The root comparison is still missing. This defines agreement
  without depending on generated identifiers or tuple order.

- **Shared witnesses.**
  [SharedWitnessExample.lean](SpytialLeanMetatheory/SharedWitnessExample.lean)
  proves a semantic example with one existential witness shared by two tuples.
  Its production connection remains open. This shows that logical sharing
  must become atom sharing.

- **Production correspondence.**
  [RuntimeCorrespondence.lean](SpytialLeanMetatheory/RuntimeCorrespondence.lean)
  proves that removing trace evidence gives the existing public API results.
  This ensures that the semantics refers to the production relationalizers.

- **Unified inspection soundness.** A new `Inspection.lean` should combine the
  computed and proof results. This is the first headline theorem and is not
  yet proved.

- **Inspection agreement.** A new `InspectionAgreement.lean` should prove
  agreement on closed values, the partial equality-refinement result, and the
  final isomorphism theorem. This is the main ICFP bridge and is not yet
  proved.

The common-reference lemma in `SemanticIsomorphism.lean` is algebraic support.
It says that two instances agree if each is already known to agree with a
third instance. It does not prove the computation/proof bridge.

## Remaining proof work

The next steps are:

1. Give the captured Lean context a `LeanExprMeaning` interpretation and state
   which successful kernel checks are trusted.
2. Prove `proposition_implies_tuple` for predicate applications and equations
   decoded as function-graph tuples.
3. Construct typed semantic instances from checked traces, provenance, and
   selector evidence. Reused atom identifiers must denote one shared typed
   atom.
4. Construct the computed structural soundness and field-coverage result from
   checked constructor and projection origins.
5. Define `inspect` for the supported core and prove inspection soundness by
   combining the computed and proof results.
6. Define `rootStruct`. The trace may need a small origin marker that
   distinguishes structure discovered from the selected root from structure
   discovered while processing an additional fact.
7. Prove the partial embedding after equality refinement. Add field coverage
   and termination to obtain the final isomorphism theorem.

Steps 1--5 establish the unified semantics and its soundness. Steps 6--7
establish the main agreement result.

## Responsibility between projects

IYKYK extracts facts from the Lean context. It owns checked proposition and
proof pairs, shared witnesses, finite extraction, inconsistent contexts, and
soundness of the extracted facts.

Spytial Lean combines computation and IYKYK facts into relational data. It
owns proposition decoding, constructor walking, tuple origins, atom sharing,
and the computation/proof bridge.

Spytial consumes the relational instance. It owns the spatial specification,
diagram refinement, layout, and rendering.

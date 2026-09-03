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

`GroundInstance` interprets each typed relation symbol. The general semantic
library allows any such interpretation. The production theorem does not take
an arbitrary interpretation. `ProductionTupleHolds` defines one relation
judgment with two rules:

- a checked structural origin establishes its represented tuple; and
- a checked proof origin establishes its represented tuple when its Lean
  proposition is true.

`ProductionTupleHolds.ground` constructs the production `GroundInstance` from
those rules. This matters: a caller cannot choose an unrelated interpretation
in which every relation is false, and no tuple certificate contains the result
that it is meant to prove.

The Lean proposition

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

These are the relations used below.

## The main theorems

The formalization now proves three headline results. Each theorem is
parametric in an interpretation of Lean expressions. That interpretation is
the trust boundary for Lean typing, definitional equality, proof checking, and
the meaning of Lean's `Eq` proposition.

### 1. Inspection is sound

```text
D = inspect(Gamma, e)       rho satisfies Gamma
-------------------------------------------------
              every tuple in D is true in rho
```

`Inspection.sound` proves this result by separating the two tuple sources.
Structural tuples use the checked constructor or projection rule.
Proof-derived tuples use the retained proof after the production checker has
checked it again. `Inspection.production_sound` combines the checked
production origins of one trace. Its conclusion uses
`ProductionTupleHolds.ground`; the theorem does not accept a `GroundInstance`
from its caller.

This result is important for partial programs and proof-constrained values:
inspection may omit information, but it must not invent information.

### 2. Inspection agrees with ordinary relationalization on values

```text
the root walk selects every ordinary atom and tuple
atom names may differ but decode to the same typed atoms
--------------------------------------------------------
rootStruct(inspect(empty, v)) ~= relationalize(v)
```

`computed_value_agreement` proves this conservativity result. The atom map is
not required to be the identity, so independently generated identifiers may
differ.

### 3. Proof refinement agrees with computation

The partial form is:

```text
Gamma proves e = v
the equality is an actual retained Afaik fact
the root walk selects a structurally closed part of relationalize(v)
inspection atom names decode back to their typed computed atoms
-----------------------------------------------------------------
rootStruct(inspect(Gamma, e)) <= relationalize(v)
```

Even if inspection stops early, every reported structural tuple agrees with
the computed value.

`ProductionRefinement.partial_bridge` proves this statement. The equality may
be written as either `e = v` or `v = e`, matching the production refinement
finder.

The complete form adds field coverage:

```text
Gamma proves e = v
the equality is an actual retained Afaik fact
every ordinary atom and structural tuple is selected
inspection atom names decode back to their typed computed atoms
----------------------------------------------------------------
rootStruct(inspect(Gamma, e)) ~= relationalize(v)
```

`ProductionRefinement.full_bridge` proves this computation/proof bridge. It
constructs both directions of the typed atom map, proves that denotations are
preserved, proves tuple preservation, and proves the two maps are inverse on
the active atoms. `ProductionRefinement.full_inspect_bridge` packages this
agreement together with denotational equality and soundness of the inspected
root tuples. Its checked structural certificate proves relationalization
soundness; `full_inspect_bridge` no longer accepts that conclusion as a
premise.

The theorem compares `rootStruct(inspect(Gamma, e))`, not the full contextual
instance. The context may legitimately add predicates and relationships that
ordinary computation does not enumerate.

Two supporting results remain important:

- facts obtained from one existential statement reuse one semantic atom for
  their shared witness; and
- deleting tuples or stopping after a justified prefix preserves soundness.

## Scope of the production result

The checked production instance covers:

- direct constructor fields and structure projections;
- predicate applications and function-graph equations decoded from proofs;
- finite walks that do not exceed their work limit; and
- atom identity policies known to preserve the represented Lean value.

The semantic theorem retains the Lean head and hidden parameters of a proved
relation. The JSON interface may deliberately group several such relations
under one display name, because Spytial consumes their union as one table.
This does not affect the typed semantic theorem. A hidden relation stamp would
only be needed for a consumer that must reconstruct the original Lean head
from JSON.

An unrestricted `SpytialIdentity` classifier may intentionally merge different
values for presentation. That merge can be useful in a diagram, but it is not
covered by the bridge. `AtomRenaming.decode_encode` states the exact supported
condition: two ordinary semantic atoms cannot collapse to one inspected atom.

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

The computed entry point runs the structural checker. The proof-context entry
point runs both the structural checker and the proof-origin checker, because a
single contextual inspection can contain tuples obtained in both ways.

`RootedTrace.lean` defines the production `rootStruct` without changing the
walker. It starts from `inspection.root` and follows checked structural edges
from source atom to child atom. Predicate and function-graph tuples are not
traversal edges. `rootStruct_subset_output` proves that every tuple reached in
this way is an actual tuple in the erased production instance. Structure found
while processing an unrelated fact is excluded unless it is structurally
reachable from the selected root.

At the semantic level, a `StructuralSelection` keeps the corresponding typed
atoms and tuples. `AtomRenaming` records how the inspection identifiers decode
to the atoms of ordinary relationalization. Interpreting the rooted production
trace supplies these two objects. The production walker does not manufacture a
second certificate or run a second relationalizer.

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
  interpretation boundary for actual Lean terms, types, definitional equality,
  proof checking, and Lean equality. The bridge derives equality of denotations
  from one checked `Eq` fact; individual bridge calls do not assume that result.

- **Production relation meaning.**
  [ProductionRelationSemantics.lean](SpytialLeanMetatheory/ProductionRelationSemantics.lean)
  defines the shared structural/proved relation judgment and constructs its
  `GroundInstance`. It also defines the typed correspondence between checked
  Lean origins and semantic tuples. These correspondences contain no
  tuple-truth field.

- **Abstract proof decoding.**
  [ProofDecoder.lean](SpytialLeanMetatheory/ProofDecoder.lean) proves soundness
  for an abstract proof-to-tuple decoder. This reuses IYKYK soundness instead
  of repeating its logic in Spytial Lean.

- **Production proof decoding.**
  [ProductionProofDecoder.lean](SpytialLeanMetatheory/ProductionProofDecoder.lean)
  connects checked production origins to typed tuples and constructs the
  abstract `ProofDecoding` result. `ProductionProofRealization.sound` derives
  tuple truth from the retained kernel-checked proof in the generated
  production ground.

- **Computed structure.**
  [ComputedRelationalization.lean](SpytialLeanMetatheory/ComputedRelationalization.lean)
  proves soundness and field coverage from the checked constructor and
  projection origins plus their typed correspondence. Its certificate has no
  `checked_origin_sound` field. These are the two directions needed for
  computed-value correctness.

- **Agreement up to atom names.**
  [SemanticIsomorphism.lean](SpytialLeanMetatheory/SemanticIsomorphism.lean)
  proves algebraic laws for typed, denotation-preserving atom maps and
  isomorphisms, including tuple mapping through inverse atom maps. This defines
  agreement without depending on generated identifiers or tuple order.

- **Unified inspection soundness.**
  [Inspection.lean](SpytialLeanMetatheory/Inspection.lean) combines structural
  and proof-derived tuples and proves `Inspection.sound` and
  `Inspection.production_sound`.

- **Computation/proof agreement.**
  [InspectionAgreement.lean](SpytialLeanMetatheory/InspectionAgreement.lean)
  proves conservativity for computed values, the partial equality-refinement
  embedding, and the complete isomorphism theorem. The final theorem obtains
  relationalization soundness from a checked structural certificate instead
  of taking it as a premise. Its `ProductionRefinement` contains an actual fact
  from the production `Afaik` result.

- **Root extraction from the real trace.**
  [RootedTrace.lean](SpytialLeanMetatheory/RootedTrace.lean) defines reachability
  through checked structural origins and proves that the root slice contains
  no tuple absent from the production output.

- **Shared witnesses.**
  [SharedWitnessExample.lean](SpytialLeanMetatheory/SharedWitnessExample.lean)
  proves a semantic example with one existential witness shared by two tuples.
  The production proof-origin checker also checks every term-to-atom link.

- **Production correspondence.**
  [RuntimeCorrespondence.lean](SpytialLeanMetatheory/RuntimeCorrespondence.lean)
  proves that removing trace evidence gives the existing public API results.
  This ensures that the semantics refers to the production relationalizers.

## Trust boundary and remaining engineering

The core bridge is proved for a checked trace and its typed realization. The
production ground is now constructed by the formalization. It is not a caller
parameter, and soundness is not a field of an individual tuple realization.

The following work remains before making the broadest claim about every
production run:

1. Construct `LeanExprMeaning`, expression-backed atoms, and the typed tuple
   realization mechanically from a checked trace. The current theorem states
   these typing and correspondence obligations explicitly. Lean's kernel,
   elaborator typing, and definitional equality remain trusted in the same way
   as the production metaprogram.
2. Package the typed realization with the exact result returned by each public
   relationalizer entry point. `RuntimeCorrespondence.lean` already proves the
   trace erases to the existing JSON result; this step adds the semantic object
   produced from that trace.
3. Add separate relation rules for observations, tabulation, synthetic edges,
   and unrestricted custom relationalizers. The current production theorem
   covers direct structure and checked proof facts.
4. Build the three evaluation domains and report when computation, partial
   structure, and proof refinement each contribute useful tuples.

## Responsibility between projects

IYKYK extracts facts from the Lean context. It owns checked proposition and
proof pairs, shared witnesses, finite extraction, inconsistent contexts, and
soundness of the extracted facts.

Spytial Lean combines computation and IYKYK facts into relational data. It
owns proposition decoding, constructor walking, tuple origins, atom sharing,
and the computation/proof bridge.

Spytial consumes the relational instance. It owns the spatial specification,
diagram refinement, layout, and rendering.

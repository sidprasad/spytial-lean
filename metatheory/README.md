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
- `D1 <= D2` means that every tuple in `D1` occurs in `D2` after one
  consistent renaming of generated atom identifiers. It does not require an
  inverse renaming; and
- `D1 ~= D2` means that the two instances have the same typed relational
  structure after renaming generated atom identifiers and reordering tuples.

These are the relations used below.

## The main theorems

The formalization now proves three headline results. Each semantic theorem is
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
checked it again. `CheckedCoreTrace.inspection_sound` applies both production
checkers, constructs the typed atoms and tuples from their checked Lean
expressions, and proves the resulting inspection sound. Its conclusion uses
`ProductionTupleHolds.ground`; the theorem does not accept a `GroundInstance`
from its caller.

This result is important for partial programs and proof-constrained values:
inspection may omit information, but it must not invent information.

### 2. Relational inspection is independent of the source of knowledge

```text
Gamma proves e = v
the rooted inspection reports every supported computed atom and tuple
---------------------------------------------------------------------
             rootStruct(inspect(Gamma, e)) ~= relationalize(v)
```

This is the main result, `RelationalInspection.knowledge_source_independence`.
The inspected and computed instances come from actual checked production
traces. The retained `Afaik` equality proves that the inspected root and the
computed term denote the same value. A two-way correspondence between their
checked structural tuples then proves that their typed relational structures
are isomorphic. Generated atom identifiers and tuple order may differ.

The partial result is:

```text
Gamma proves e = v
the root walk may stop before reporting every computed tuple
-------------------------------------------------------------
rootStruct(inspect(Gamma, e)) <= relationalize(v)
```

`RelationalInspection.agrees_with_computation` proves this one-way result. It
says that inspection agrees with computation on everything that inspection
reports. It does not say that every computed tuple was reported, or that two
different inspection atoms remain different after their identifiers are
renamed.

The theorem compares `rootStruct(inspect(Gamma, e))`, not the full contextual
instance. The context may legitimately add predicates and relationships that
ordinary computation does not enumerate.

Two supporting results remain important:

- facts obtained from one existential statement reuse one semantic atom for
  their shared witness; and
- deleting tuples or stopping after a justified prefix preserves soundness.

### 3. Semantic relations project to Spytial relations by name

The semantic layer keeps the full Lean relation head and hidden parameters.
The display layer intentionally keeps only the short relation name:

```text
semantic R1 --\
semantic R2 ----> rows named R ----> one Spytial relation R
semantic R3 --/
```

Each displayed row retains its own typed schema. Therefore relations with the
same name may have different column types or arities. This is not a collision:
Spytial relations are ragged and each tuple is self-describing. A malformed
row with a different number of atoms and types is rejected at the shared
insertion boundary.

`Inspection.named_presentation_union` proves that, for every display
name, the displayed rows are exactly the structural rows with that name plus
the proof-derived rows with that name. The projection neither drops nor
invents a row. `CheckedCoreTrace.sound_and_presentation_union` packages this
with semantic soundness of the checked inspection. No renderer change is
required.

## Scope of the production result

The checked production instance covers:

- direct constructor fields and structure projections;
- predicate applications and function-graph equations decoded from proofs;
- finite walks that do not exceed their work limit; and
- atom identity policies known to preserve the represented Lean value.

The semantic theorem retains the Lean head and hidden parameters of a proved
relation. The JSON interface deliberately groups several such relations under
one display name, because Spytial consumes their union as one table. Each tuple
retains its own types, and a relation with more than one tuple width has an
empty relation-level type summary. This does not affect the typed semantic
theorem. A hidden relation stamp would only be needed for a consumer that must
reconstruct the original Lean head from JSON.

An unrestricted `SpytialIdentity` classifier may intentionally merge different
values for presentation. That merge can be useful in a diagram, but it is not
covered by the comparison theorem. `RelationalInspection.CompleteCoverage`
states the exact supported condition: computation has no additional tuple and
the identifier renamings are inverse on the active atoms of both results.

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

The checker retains a `CheckedColumn` for each aligned term and atom ID. A
`CheckedColumn` can be created only after Lean has inferred the term's type.
`ProductionTraceInstance.lean` recursively turns these checked columns into an
intrinsically typed tuple. This construction supplies the typing, relation,
atom-ID, and term-correspondence fields that earlier results took as separate
premises.

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

At the semantic level, `rootedStructuralTuples` interprets the reachable
origins directly. `RelationalInspection.ReportedStructure` records a concrete
renaming of generated atom identifiers and checks that every reported tuple
occurs in the computed trace after that renaming. `CompleteCoverage` adds the
reverse direction and requires the two renamings to be inverse on active atoms.
The semantic homomorphism and isomorphism are derived from these syntactic
facts; they are not fields of the production correspondence. The public walker
does not run a second relationalizer.

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
  proof checking, and Lean equality. The knowledge-source theorem derives
  equality of denotations from one checked `Eq` fact; individual theorem calls
  do not assume that result.

- **Production relation meaning.**
  [ProductionRelationSemantics.lean](SpytialLeanMetatheory/ProductionRelationSemantics.lean)
  defines the shared structural/proved relation judgment and constructs its
  `GroundInstance`. It also defines the typed correspondence between checked
  Lean origins and semantic tuples. These correspondences contain no
  tuple-truth field.

- **Checked production instance.**
  [ProductionTraceInstance.lean](SpytialLeanMetatheory/ProductionTraceInstance.lean)
  runs both built-in trace checkers and constructs expression-backed semantic
  tuples from their checked columns. `CheckedCoreTrace.inspection_sound` proves
  soundness directly. It has no per-origin realization premise and does not
  require a certificate from a custom relationalizer.

- **Presentation projection.**
  [PresentationProjection.lean](SpytialLeanMetatheory/PresentationProjection.lean)
  replaces internal relation identity by the short Spytial name while
  retaining each tuple's own typed schema. It proves row preservation,
  same-name coalescing, and union of the computed and proof-derived rows.

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
  proves `RelationalInspection.agrees_with_computation` for partial results and
  `RelationalInspection.knowledge_source_independence` for complete results.
  The latter is the paper-facing theorem: a value has the same root relational
  structure whether Lean obtains it by computation or by a checked equality.
  Its `ProductionRefinement` contains an actual fact from the production
  `Afaik` result.

- **Root extraction from the real trace.**
  [RootedTrace.lean](SpytialLeanMetatheory/RootedTrace.lean) defines reachability
  through checked structural origins, constructs the typed semantic inspection
  of that root, and proves it sound. It also proves that the root slice contains
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

The built-in structural and proof checkers now construct the semantic
inspection from the real trace. The production ground is also constructed by
the formalization. Neither tuple truth nor tuple realization is supplied by a
caller.

`ProductionEvidenceMeaning` states one connection between successful Lean
checks and the abstract interpretation of Lean expressions. In particular, a
term accepted by `inferType` has that type in the interpretation, and a proof
accepted for a proposition satisfies `LeanExprMeaning.proofChecks`. These are
global laws about Lean's checker. They are not repeated for each tuple. Proving
them inside this project would require proving Lean's elaborator and kernel
correct inside Lean, which is intentionally outside the model.

The following work remains before making the broadest claim about every
production run:

1. Add separate relation rules for observations, tabulation, synthetic edges,
   and unrestricted custom relationalizers if future claims need them. The
   current theorem deliberately covers only the checked built-in structural
   and proof paths.
2. Build the three evaluation domains and report when computation, partial
   structure, and proof refinement each contribute useful tuples.

## Responsibility between projects

IYKYK extracts facts from the Lean context. It owns checked proposition and
proof pairs, shared witnesses, finite extraction, inconsistent contexts, and
soundness of the extracted facts.

Spytial Lean combines computation and IYKYK facts into relational data. It
owns proposition decoding, constructor walking, tuple origins, atom sharing,
and agreement between computation-guided and proof-guided inspection.

Spytial consumes the relational instance. It owns the spatial specification,
diagram refinement, layout, and rendering.

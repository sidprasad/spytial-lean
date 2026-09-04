# Semantics and correctness of relationalization

## Why Spytial in Lean is interesting

> A value can be inspected using knowledge obtained either by computation or
> by proof.

Lean presents values in several forms. A value may be fully evaluated. It may
contain a stuck or symbolic program. It may also occur in a proof context that
establishes facts that evaluation alone cannot recover.

Spytial can give these cases one relational interface:

```text
computed value       partial program       proof-constrained value
      |                     |                        |
      +-------------- relational instance ----------+
                             |
                  same Spytial specification
                             |
                          diagrams
```

The instances do not need to contain the same tuples. A proof context may add
facts, and a bounded computation may expose only part of a value. The important
point is that all sources produce the same kind of typed relational data. A
domain therefore needs one Spytial specification, not one renderer for values,
one for stuck programs, and another for proof states.

This directory gives a semantics to that relationalization step. Spytial still
owns selection, spatial constraints, layout, and rendering.

## The operation being modelled

We write the operation as:

```text
inspect(Gamma, e) = D
```

`Gamma` is a Lean proof context, `e` is the selected term, and `D` is a finite,
typed, positive relational instance.

The production proof-guided inspector has two relevant phases:

```text
checked facts in Gamma
          |
          v
find a value for e ----> run the ordinary structural walker
                                      |
                                      v
                              root structure
                                      |
                                      v
                         add checked contextual facts
                                      |
                                      v
                              full inspection D
```

The implementation retains the state immediately after the structural walk.
The correspondence checker also makes a fresh call to the ordinary production
relationalizer on the value found for `e`. This is not a second formal model:
both traces come from the code used by Spytial Lean. The public JSON result is
unchanged.

The formalization distinguishes the completed inspection, the structural
trace retained before contextual facts are added, and the fresh structural
trace returned by the independent production call.

The full inspection need not equal computation. Proofs may legitimately add
relations and the structure needed to display their arguments. The theorem is
that proof guidance does not replace or reinterpret the root computation.

## Positive and partial information

An atom represents a typed Lean term. A tuple states that a typed relation
holds of its atoms. An origin records why the relationalizer emitted it.

Presence is meaningful: every supported emitted tuple must be justified.
Absence is not negative information. If a tuple is missing, the semantics does
not say that the relation is false.

The model follows IYKYK's context semantics. A `World` is an interpretation of
the free terms. `context world` says that the interpretation satisfies
`Gamma`. A symbolic atom may denote different values in different compatible
worlds; every use of the same atom denotes the same value within one world.

`LeanExprMeaning.ground` supplies the relation interpretation used by the
production theorems. It is part of the meaning of Lean expressions and is
independent of every finite trace. A trace cannot make a tuple true merely by
containing it.

Opaque tokens record successful production checks. The semantic assumptions
are implications from those tokens: a token for `term : type` means that the
term has that type, and a token for definitional equality means that the two
expressions have the same meaning. The rules for proof and structural origins
then connect checked Lean syntax to the independent ground relation.

## Main results

### The supported production inspection is sound

```text
D = inspect(Gamma, e)       world satisfies Gamma
--------------------------------------------------
          every supported tuple in D holds
```

`CheckedCoreTrace.inspection_sound` constructs typed semantic tuples from the
actual checked production origins. `RelationalInspection.KnownValue.sound`
applies this result to the complete trace of a proof-guided run. It includes
all direct constructor or projection origins and all checked proof origins.

This theorem is one-way because the instance is partial. It proves that the
inspector does not invent supported tuples; it does not treat omitted tuples
as false.

### Proof-guided inspection agrees with a fresh relationalization

The correspondence entry point is:

```text
CheckedFreshRelationalization.inspect :
  (knowledge : Iykyk.Afaik) ->
    MetaM (CheckedFreshRelationalization knowledge)
```

It first performs proof-guided inspection. Lean checks how the selected root is
related to the value used by the structural walk. The relation may follow from
computation or from an equality proof in the context. It then calls
`relationalizeWithTrace` again on that value and checks the two structural
traces against each other.

The paper-facing theorem is:

```text
proof_guided_inspection_agrees_with_fresh_relationalization
```

Its structural part is also available directly as
`fresh_relationalization_agrees_with_inspection_root`.

Its conclusion has three parts:

```text
Lean establishes that e denotes the computed value, by computation or proof
the completed inspection retains the structural rows from its root walk
root trace from inspect(Gamma, e) ~= fresh relationalize(value)
```

`~=` means that the traces agree row for row after a two-sided renaming of
generated atom identifiers. Corresponding rows have the same relation name,
structural rule, Lean relation head, source, child, column terms, and column
types. Lean expressions are compared by checked definitional equality.

The theorem has only two explicit inputs:

1. the checked pair returned by `CheckedFreshRelationalization.inspect`; and
2. one interpretation of the opaque Lean check tokens.

It has no premise supplied by the caller for field coverage, tuple
correspondence, atom renaming, root equality, or structural agreement. The
production checker constructs those facts. In particular, it directly checks
`computedChecked` against the first structural rows of `structuralChecked`; the
theorem does not silently identify those two traces.

The computation branch covers both a fully evaluated value and a stuck term:
in each case the selected root is definitionally equal to the expression
represented by the walker. The proof branch covers a symbolic root whose
value is supplied by a checked equality in `Gamma`.

The statement applies to every successful checked pair. It does not require a
caller-supplied `CompleteCoverage` premise: both sides compare the finite rows
that the production walks actually emitted. The current theorem covers the
direct structural core and excludes requested observations. The regression
test in `tests/InContextTest.lean` exercises a computed value, a stuck symbolic
value, a structure projection, and a proof-refined value.

### Semantic relations project to Spytial relations

The semantic layer keeps the full Lean relation head and its hidden
parameters. The presentation layer uses the short Spytial relation name:

```text
semantic R1 --\
semantic R2 ----> displayed rows named R
semantic R3 --/
```

Each row retains its own typed schema. Several Lean relations may therefore be
shown as one Spytial relation without losing or inventing rows.
`Inspection.named_presentation_union` proves this union property, and
`CheckedCoreTrace.sound_and_presentation_union` combines it with production
soundness. No renderer change is required.

## Why the theorem is tied to production

The checkers store opaque evidence tokens for the facts that matter:

- `CheckedColumn` contains successful type-check evidence;
- `CheckedStructuralTrace` comes from the structural origin and field-coverage
  checker;
- `CheckedProofTrace` comes from rechecking proof origins and their decoded
  terms;
- `CheckedComputedValue` contains the type and definitional-equality checks
  between the root and computed term;
- `CheckedEqualityRefinement` comes from checking an actual retained equality
  against the computed term;
- `CheckedKnownValueInspection` pairs that equality with the run that it
  checked; and
- `CheckedFreshRelationalization` contains a fresh production trace and the
  checked two-way atom and row correspondence.

Constructor privacy is not the logical argument. The evidence types themselves
are opaque, and their public checkers return tokens only after the relevant
Lean or production check succeeds. `RuntimeCorrespondence.lean` proves that
erasing the retained phase gives the established trace and JSON APIs.

## Files and what they establish

- `SemanticInstance.lean` defines typed atoms, tuples, positive relational
  instances, and partial-instance soundness. This is the common output type for
  computation and proof.

- `LeanExprMeaning.lean` defines the interpretation of actual `Lean.Expr`
  terms, types, definitional equality, checked proofs, and Lean equality.

- `RelationalInstance.lean` and `RuntimeCorrespondence.lean` connect semantic
  tuple membership to the production trace and its JSON erasure.

- `ProductionRelationSemantics.lean` defines the shared meaning of checked
  structural and proof-derived origins. The ground relation comes from
  `LeanExprMeaning`, not from emitted tuples.

- `ProductionTraceInstance.lean` converts the actual checked origins into
  intrinsically typed semantic tuples and proves the resulting production
  instance sound.

- `SpytialLean/StructuralCorrespondence.lean` reruns the ordinary production
  relationalizer and checks row, expression, type, and atom correspondence.

- `ComputedRelationalization.lean` proves soundness and supported first-order
  field coverage for checked structural origins.

- `Inspection.lean` combines structural and proof-derived tuples into one
  positive instance.

- `InspectionAgreement.lean` proves equality of denotations from the checked
  retained equality, soundness of the complete supported inspection, and the
  final computation/proof correspondence theorem.

- `FreshStructuralCorrespondence.lean` interprets the checked two-way mapping
  between the retained trace and the fresh production trace and proves
  `fresh_relationalization_agrees_with_inspection_root`. It also proves that
  the completed contextual trace retains the root phase.

- `SemanticIsomorphism.lean` defines agreement independently of generated atom
  identifiers and tuple order.

- `PresentationProjection.lean` proves that projection to short Spytial names
  preserves exactly the rows produced by both knowledge sources.

- `SharedWitnessExample.lean` shows that facts obtained from one existential
  statement reuse one semantic witness.

## Trust boundary

The semantic result is parametric in `LeanExprMeaning`. This is the standard
boundary around Lean's elaborator and kernel: a term accepted by type inference
has its inferred type, definitionally equal terms have the same denotation, and
a checked proof makes its proposition true in every compatible world.

`ProductionEvidenceMeaning` states these laws once as implications from opaque
production tokens. It also states how checked proposition and structural
shapes are interpreted by the independent ground relation. It does not assume
the fresh correspondence: that correspondence is checked separately and then
proved to have the stated semantic meaning. Proving the token laws inside this
project would require a correctness proof for Lean's elaborator and kernel.

The current production soundness result covers the built-in direct structural
and checked-proof origins. Symbolic function graphs, observations, tabulation,
synthetic display edges, unrestricted custom relationalizers, and deliberately
value-merging custom identity policies need their own semantic rules before a
claim includes them. They are not assumptions of the theorem above.

## Responsibility between projects

IYKYK extracts checked facts and witnesses from the Lean context. It owns proof
search, context consistency, finite extraction, and the soundness of extracted
facts.

Spytial Lean turns computed structure and IYKYK facts into one relational
instance. It owns proposition decoding, constructor walking, tuple origins,
atom reuse, the computation/proof agreement theorem, and projection to the
Spytial table format.

Spytial consumes that relational instance. It owns specifications, diagram
refinement, layout, and rendering.

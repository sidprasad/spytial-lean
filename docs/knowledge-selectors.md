# Select from what the proof establishes

In a proof, a node can have a known property without being a known value.
Given `h : height t = 3`, Spytial can select `t` even if its children are unknown:

```lean
spytial t with [
  atomStyle known (fun n : Tree => height n = 3) (fillStyle "#dbeafe")
]
```

`known (…)` is a predicate over represented Lean terms, matched against the
facts extracted by IYKYK. It needs neither a complete value of `t` nor compiled
evaluation of `height t`. A `lean (…)` selector still executes a predicate on
closed values; the two forms are deliberately different.

This is initial support for [selectors over partially known values](https://github.com/sidprasad/spytial-lean/issues/60),
not an interpreter for arbitrary `Spytial.Sel` programs.

## The contract

For a predicate `p : T₁ → … → Tₙ → Prop`, a tuple of existing atoms is selected
when both conditions hold:

1. Each atom has a represented Lean term `eᵢ` of the corresponding type `Tᵢ`.
2. An extracted, certified fact has a proposition definitionally equal to
   `p e₁ … eₙ`.

Matching uses Lean's definitional equality, including unfolding definitions
and beta reduction. It does not perform further theorem search, equality
rewriting, or logical composition. For example, separate facts `P x` and
`Q x` do not by themselves match `known (fun x => P x ∧ Q x)`. Intersect
`known (P) & known (Q)` instead. IYKYK's extraction still supplies its usual
simplification and forward rules; use `fyi` to supply rules or proved facts.

The terms can include symbolic variables, partially determined constructors,
and shared existential witnesses. Refinement retains the original term's
association with its drawn atom. If identity merges multiple terms into one
atom, evidence about any represented term selects that atom, once; this does
not assert that the property holds for every term in the identity class.
Custom emissions without a corresponding walked Lean term cannot be selected.
Type matching uses actual Lean types, not diagram labels or short names.

## Unknown is not false

If no extracted fact matches `P x`, `x` is not selected. This is absence of
support, not evidence of `¬ P x`. The selector `known (fun x => ¬ P x)` needs
its own matching fact. Negative facts can support selectors even though they
are not drawn as unconditional relation edges.

Relational set operations keep their ordinary meaning: `univ - known (P)` is
the set of atoms *not selected by the available evidence*. It is **not** the
set known to satisfy `¬ P`. Extraction is bounded and rooted at the inspected
term, so even facts elsewhere in the context need not be available here.

## Inline and attached specifications

The same selector can be attached to a type and resolved at each inspection:

```lean
spytial_spec Tree [
  atomStyle known (fun n : Tree => height n = 3) (fillStyle "#dbeafe")
]

example (t : Tree) (h : height t = 3) : True := by
  spytial t
  trivial
```

Inline predicates may capture proof-local parameters, such as a relation
`edge : Vertex → Vertex → Prop`. Binary and wider predicates select tuples,
so `inferredEdge path known (edge)` can draw precisely the supported pairs.
The usual selector operators, layout operations, and source reporting apply.

## Deliberate limits of this draft

- Tactic mode only. `#spytial` has no extraction; encountering `known`,
  including through an attached spec, is an explicit error.
- Predicates return `Prop`, have one to four non-dependent arguments, and
  need no `Decidable` or `BEq` instance. Unresolved holes are not matched or solved.
- Selection is capped at 4,096 tuples and one million candidate/fact comparisons.
  Limits fail explicitly rather than returning a partial selection.
- Existing `lean` behavior is unchanged. In particular, an attached
  whole-value `Spytial.Sel` still fails if the root is not fully determined;
  Spytial never silently substitutes an empty selection.

The draft leaves richer entailment and a command-mode interpretation open.

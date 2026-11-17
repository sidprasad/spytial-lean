# What `observing` means

`observing [f]` asks for the value of `f t` for each applicable value `t`
already represented in the inspection:

```lean
spytial tree observing [height]
```

Observation retains a checked symbolic residual when the result is not
concrete. Deterministic results are displayed as expressions over genuinely
unknown observation leaves, rather than as unrelated fresh values.

## Observing a predicate

A named predicate can appear alongside a data-returning function:

```lean
spytial x observing [parent, Reaches parent]
```

`parent` contributes a pointer for each represented vertex. Applying `Reaches`
to that particular map leaves two vertex arguments. The observation produces a
binary relation named `Reaches parent`. A proof of `Reaches parent x rx` puts
`(x, rx)` in it even if the proof context gives no individual steps of that path.
The relation exists in the datum and can be styled with
`edgeStyle «Reaches parent» (lineStyle dashed)`.

An observation can also establish new tuples. Given `parent a = b` and
`parent b = c`, the constructors `Reaches.step` and `Reaches.refl` provide a proof
of `Reaches parent a c`. The inspector checks the proof with Lean's kernel.
For an opaque path followed by one pointer, the union-find demo supplies the
ordinary path-extension lemma through `fyi [Reaches.append_step (parent := joined)]`.
This lets it display `Reaches joined x ry` before the proof names that fact.

The candidates are tuples of compatible atoms in the datum, including represented
results of value observations. Predicates accept one to four nondependent arguments.
For each candidate, the observer tries retained evidence, simplification, and
bounded search using the predicate's constructors. Search has depth eight and
enumeration allows up to 4,096 candidates per predicate. An absent tuple means
the observation found no proof. Observations add no hypotheses to the Lean goal.

## Stages of a value observation

Observation has five internal stages:

1. **Domain discovery.** Spytial snapshots the represented values to which each
   requested unary function applies.
2. **Residualization.** It simplifies each application using definitions and,
   in tactic mode, retained proof-backed facts. The result carries a checked
   equality from the source application to its residual expression.
3. **Focused questions.** Spytial recognizes propositions that could unblock
   the residual. For a symbolic `max a b`, it may ask Lean to prove `a ≤ b`
   or `b ≤ a` using bounded `simp` and `omega` queries. Successful
   checked proofs are fed back into simplification; unsuccessful queries leave
   the expression symbolic.
4. **Proof-backed normalization.** Arithmetic normalizers may propose a more
   compact residual, such as replacing `1 + (x + 2)` with `x + 3`. Spytial
   accepts the replacement only when Lean produces a proof of equality and
   composes that proof with the residualization evidence.
5. **Relationalization and presentation.** Unknown observation leaves receive
   shared symbolic atoms. A generic renderer asks Lean for each application's
   notation, tracks whether children are atomic or compound, and groups
   compound children structurally. It contains no formatting rules for
   particular functions or operators. The final result is connected to its
   input by the requested observation relation and emitted with the rest of
   the datum.

The focused queries do not enlarge the retained context evidence. They only help
normalize the observation result before the final datum is produced.

## Relational contract

Let `D` be the finite collection of represented values before observations are
added. In command mode these come from the selected expression. In tactic mode
they also include values represented by the retained, certified context facts.
`D` is not every variable of a matching type in the local context.

For every requested unary function `f : A → B` and every represented `t : A`:

1. Form `f t` and simplify it to a residual `r`.
2. Retain checked evidence of `Γ ⊢ f t = r`. If no computation is possible,
   `r` can be `f t` itself.
3. In tactic mode, ask only focused questions discovered from `r`, then
   re-simplify with any checked answers.
4. Represent the result and add `f(t, result)`, reusing the existing atom for
   `t`.

Concrete results are ordinary values such as `2`. An irreducible observed
application receives a neutral display name such as `¿x?`. Existential
witnesses retain their source binder (`¿middle?` for `∃ middle, ...`); a
genuinely anonymous witness joins the same neutral sequence. The surrounding
question marks distinguish generated names from ordinary variables. Distinct
letters carry the common-case difference; numeric subscripts appear only after
the letter supply is exhausted or when a binder repeats. A generated label
does not repeat an application's source expression: the incoming relation
already records that provenance, and more than one relation may eventually
refer to the same atom. A deterministic residual is proof-normalized before
being labelled by an expression over those shared names. For example:

```text
height(l)      = ¿x?
height(r)      = ¿y?
height(parent) = (max ¿x? ¿y?) + 1
```

If the context proves enough arithmetic relationships, the same result can be
more compact:

```text
height(before) = ¿x? + 3
height(after)  = ¿x? + 2
```

These labels are not assignable Lean metavariables. Each atom retains the
actual Lean expression and the observation equality remains proof-backed.
Occurrences of the same named application reuse its result atom, so context
facts and observations refer to the same value.

The represented domain is fixed before observation results are added. Thus
observing `bump : Nat → Nat` at `1` adds `bump(1, 2)`, not an infinite sequence
of newly observed results.

## Focused proof questions

Spytial discovers propositions that would unblock an observed computation.
Its query helpers pass those propositions and the retained proof terms to Lean
automation, then kernel-check successful proofs in the original scope.

The first supported blocker is `max` over `Nat` or `Int`:

```text
residual contains max a b
Spytial asks       a ≤ b  or  b ≤ a
Lean returns       proved / not proved / truncated
```

This is goal-directed rather than arithmetic saturation. Spytial does not attempt
to enumerate all consequences of the context, and failure to prove one ordering
is not evidence for the other. The query loop and each proof attempt are bounded.

Whole-value command mode performs definition reduction and ordinary
simplification without collecting local proof evidence.

## Why `max` and addition are not observers

Writing `observing [height, max, HAdd.hAdd]` would have different semantics.
`height` is a unary function mapped over a fixed domain. `max` and addition are
binary operations that occur at particular places in `height`'s residual.
Observing them independently would require a Cartesian product of represented
numbers and would produce combinations never used by the height computation.

Spytial instead retains the particular operations already present in the
checked residual. They do not require public observation options.

## Height example and its limits

For a right rotation, let:

```lean
a := height ll
b := height lr
c := height r
```

The tree shape alone establishes:

```text
height before = 1 + max (1 + max a b) c
height after  = 1 + max a (1 + max b c)
```

It does not order `a`, `b`, and `c`. If the context additionally proves
`a = b + 1` and `b = c`, Lean arithmetic automation can discharge the relevant
comparisons and the labels normalize to `c + 3` and `c + 2`. Without those facts,
the maxima remain.
Arithmetic derives consequences; it does not invent AVL preconditions.

## Limits and ownership

- Observation evaluation and focused-question discovery belong to Spytial.
- Aesop schedules forward rules and simplification; Lean provides arithmetic
  proof search. Spytial bounds these calls, exports their proofs to the original
  scope, and checks evidence before using it.
- Final atom identity, expression labels, relations, and presentation belong
  to Spytial.
- Evaluation remains best-effort and bounded. Opaque bodies, unavailable
  definitions, and computations requiring unknown data can remain symbolic.
- Existing metavariables are not assigned, and fresh unresolved metavariables
  cannot escape observation preparation.
- Structured results retain their ordinary constructor fields.
- `with [attribute height]` changes presentation, not the observation or proof
  process.

Regressions live in `SpytialTests/ContextInspectionTest.lean`,
`SpytialTests/InContextTest.lean`, and `SpytialTests/TacticTest.lean`.

# What `observing` means

`observing [f]` asks for the value of `f t` for each applicable value `t`
already represented in the inspection:

```lean
spytial tree observing [height]
```

Observation retains a checked symbolic residual when the result is not
concrete. Deterministic results are displayed as expressions over genuinely
unknown observation leaves, rather than as unrelated fresh values.

## Stages

Observation has four internal stages:

1. **Domain discovery.** Spytial snapshots the represented values to which each
   requested unary function applies.
2. **Residualization.** It simplifies each application using definitions and,
   in tactic mode, retained proof-backed facts. The result carries a checked
   equality from the source application to its residual expression.
3. **Focused questions.** Spytial recognizes propositions that could unblock
   the residual. For a symbolic `max a b`, it may ask IYKYK to prove `a ≤ b`
   or `b ≤ a` using its bounded `simp` and `omega` query mechanisms. Successful
   checked proofs are fed back into simplification; unsuccessful queries leave
   the expression symbolic.
4. **Relationalization.** The final result is connected to its input by the
   requested observation relation and emitted with the rest of the datum.

The focused queries do not add facts to the inspected `Afaik`. They only help
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
application receives a generated display name such as `?₁`. A deterministic
residual is labelled by an expression over those shared names. For example:

```text
height(l)      = ?₁
height(r)      = ?₂
height(parent) = (max ?₁ ?₂) + 1
```

If the context proves enough arithmetic relationships, the same result can be
more compact:

```text
height(before) = ?₁ + 3
height(after)  = ?₁ + 2
```

These labels are not assignable Lean metavariables. Each atom retains the
actual Lean expression and the observation equality remains proof-backed.
Occurrences of the same named application reuse its result atom, so context
facts and observations refer to the same value.

The represented domain is fixed before observation results are added. Thus
observing `bump : Nat → Nat` at `1` adds `bump(1, 2)`, not an infinite sequence
of newly observed results.

## Focused proof questions

Spytial, not IYKYK, decides which propositions would unblock an observed
computation. IYKYK receives ordinary propositions and returns checked proofs;
it knows nothing about trees, heights, or visualization.

The first supported blocker is `max` over `Nat` or `Int`:

```text
residual contains max a b
Spytial asks       a ≤ b  or  b ≤ a
IYKYK answers      proved / not proved / truncated
```

This is goal-directed rather than arithmetic saturation. Spytial does not ask
IYKYK to enumerate all consequences of the context, and failure to prove one
ordering is not evidence for the other. The query loop and each proof attempt
are bounded.

Command mode has no `Afaik`, so it performs definition reduction and ordinary
simplification but no context-backed IYKYK queries.

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
`a = b + 1` and `b = c`, IYKYK can discharge the relevant comparisons and the
labels normalize to `c + 3` and `c + 2`. Without those facts, the maxima remain.
Arithmetic derives consequences; it does not invent AVL preconditions.

## Limits and ownership

- Observation evaluation and focused-question discovery belong to Spytial.
- Proof search, bounds, captured scope, and kernel certification belong to
  IYKYK.
- Final atom identity, expression labels, relations, and presentation belong
  to Spytial.
- Evaluation remains best-effort and bounded. Opaque bodies, unavailable
  definitions, and computations requiring unknown data can remain symbolic.
- Existing metavariables are not assigned, and fresh unresolved metavariables
  cannot escape observation preparation.
- Structured results retain their ordinary constructor fields.
- `with [attribute height]` changes presentation, not the observation or proof
  process.

Regressions live in `tests/ContextInspectionTest.lean`,
`tests/InContextTest.lean`, and `tests/TacticTest.lean`.

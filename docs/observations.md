# What `observing` means

`observing [f]` asks for the value of `f t` for each applicable value `t`
already represented in the inspection. It does not ask for a trace of how
`f` computes that value.

## Relational contract

Let `D` be the finite collection of represented values before adding
observations. In command mode these come from the selected expression. In
tactic mode they also include values represented by the retained, certified
context facts. `D` is not every variable of a matching type in the local context.

For every requested unary function `f : A → B` and every represented `t : A`:

1. Form `f t` and try to evaluate it using available definitions, ordinary
   simplification rules, and the retained context proofs.
2. Obtain a result expression `r` with a checked equality `Γ ⊢ f t = r`.
   If no computation is possible, `r` can simply be `f t` itself.
3. Represent the result in the same datum and add the tuple
   `f(t, result)`, using the existing atom for `t`.

Concrete results are ordinary values, such as the number `2`. A result known
to equal a local value uses that value. Known result constructors retain their
ordinary fields, including symbolic fields. An unresolved computation has a
symbolic result atom (`?₁`, `?₂`, …), not an automatically expanded computation graph.
Occurrences of a named application share its result, so a context comparison
and an observation refer to the same value.

These are display labels, not assignable Lean metavariables. The subscript
distinguishes values within one inspection; repeated references to the same
atom keep the same label.

The existing type/relationalizer identity policy still determines which input
values share atoms. Observing does not override an occurrence-based policy.
The domain is fixed before observation results are introduced: observing
`bump : Nat → Nat` at `1` adds `bump(1, 2)`, not an infinite chain of observations.

## Evaluation is not an extra observation

For `height (node l key r)`, evaluation can use
`1 + max (height l) (height r)` internally. That does not request `add` or `max`
relations, any more than it requests the internal constructors of `Nat`.

Other relations can come from explicit inspected expressions and retained
proof-backed facts. For example, a branch fact
`height r + 1 < height l` connects the height results through `add` and `lt`.
That relationship is present in the context being inspected; it is not an
automatic expansion of the observer's defining equation.

Merely being able to prove a defining equation does not select it for display.
General automatic discovery/selection of further relations is not part of
`observing`. The current syntax accepts named unary data-returning functions;
it does not yet accept binary `add` as an observer over pairs of domain values.

## Examples with height

Here `singleton key := node leaf key leaf` is an ordinary helper definition.

| Represented tree / available facts | Observed height |
| --- | --- |
| `leaf` | `0` |
| `singleton key`, with unknown `key` | `1` |
| `node (singleton key) x leaf` | `2` |
| `node l key r`, with arbitrary `l` and `r` | Symbolic |
| Same tree, with `height l = 2`, `height r = 1` | `3` |
| Same tree, with only `height r + 1 < height l` | Generally still symbolic |

This is why evaluating the observation, rather than demanding a completely
concrete input tree, matters: `height` does not need the node keys.

In the generic AVL rotation/balance definitions, subtrees such as `ll`, `a`,
`b`, and `r` are arbitrary trees, not known leaves. The branch conditions do
not determine absolute heights. A concrete example can therefore show numeric
before/after heights while the generic branch still shows symbolic heights
and the comparisons supplied by its context. For example, two concrete LR
inputs can have before/after heights `3 → 2` and `4 → 3` respectively.

## Limits and ownership

- Evaluation is best-effort and bounded by the simplifier step limit and Lean's
  reduction/heartbeat limits. It is not a promise of a complete normal form.
  Recoverable preparation failures retain the application symbolically with a
  warning; exhausting Lean's overall resource limits can stop the inspection.
- Computation follows available, transparent Lean definitions. Opaque bodies,
  unavailable definitions, and computations needing unknown data may remain
  symbolic. No compiled runtime default is substituted for unknown data.
- Simplification can use certified facts; it does not perform unrestricted
  theorem search or invent branch preconditions. Observation is not a proof
  that a rotation preserves balance.
- Existing metavariables are not assigned, and fresh unresolved metavariables
  cannot escape evaluation. The proof state is unchanged. Applications with
  unresolved universe metavariables currently skip preparation.
- The existing finite context-fact selection still applies. Observation does
  not rerun IYKYK to discover new facts about its newly produced values.
- `with [attribute height]` controls presentation, not evaluation. A symbolic
  height may still display as `?₁`; pretty-printing its residual formula as an
  attribute would be a separate presentation feature.

This behavior belongs to Spytial's Lean relationalizer. IYKYK supplies checked
context facts; it does not need a new inference mechanism to evaluate a
requested function application. No new `observing` option is required.

Regressions live in `tests/ContextInspectionTest.lean`, `tests/InContextTest.lean`,
and `tests/TacticTest.lean`.

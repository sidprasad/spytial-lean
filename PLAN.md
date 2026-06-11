# spytial-lean roadmap plan

This document records the design decisions for the open issue backlog and tracks
implementation status. It is maintained in-repo so decisions survive the PRs that
implement them. Last updated: 2026-06-11.

## Status at a glance

| Issue | Feature | Status |
|-------|---------|--------|
| #22 | DAG-shared subterm flag | ✅ done |
| #9 | Quotient type visualization | ✅ done |
| #21 | Indexed-family index labels | ✅ done |
| #13 | Structural function-body decomposition | ✅ done |
| #8 | `#spytial.enumerate` finite types | ✅ done |
| #24 | `.notationLabel` surface-syntax collapse | ✅ done |
| #2 | Type-class spec inheritance | ✅ verified; rest deferred |
| #23 | `maxAtoms` guard + benchmarks | ✅ done |
| #10 | `spytial_goals` proof-state tactic | ✅ done (experimental) |
| #20 | Mathlib smoke-test demo | 🔵 deferred (separate project) |

Each landed feature ships with a demo under `demos/` registered in the `Demos`
lib roots, and was verified with `lake build` + `lake build Demos`.

## Guiding principles

1. **Selectors must stay stable.** The `type` field of an atom is part of the
   user-facing spec API (selectors match on it). Features may enrich *labels*
   freely, but must not change existing `type` strings or relation names.
2. **No Mathlib dependency in the core library or default demos.** Anything that
   needs `Fintype`, `Subgroup`, etc. lives in a separate, optional project.
3. **Relationalizer behavior changes must be strict improvements.** Where a term
   today renders as an opaque leaf, decomposing it further is fine. Where it
   already decomposes, the default output must not change shape (opt-in only).
4. **Spec ops that affect the relationalizer (not the widget) are partitioned
   out of the YAML** and become `WalkConfig` fields. The YAML remains exactly
   what spytial-core's `parseLayoutSpec` understands.

## Decisions and status

### #22 — Surface DAG-shared subterms — **DONE (this PR)**

**Decision: Option 1 (shared flag), least invasive.**
`WalkState.seen` already deduplicates by `Expr.hash`. On a second visit we now
mark the existing atom `shared := true`. `JsonAtom.shared` serializes as an
extra JSON field, which spytial-core ignores today; the flag is visible in
`#spytial.datum` output, and a `demos/Sharing.lean` demo documents the
behavior. Distinct visual styling (dashed border) belongs in spytial-core and
is deferred there — the data already carries the flag it would need.

### #9 — Quotient type visualization — **DONE (this PR)**

**Decision: detect `Quot.mk`-headed terms, walk the representative.**
`Quot` is kernel-primitive (`.quotInfo`, not `.ctorInfo`), so the constructor
dispatch misses it and it falls through to an opaque leaf. We special-case
applications headed by `Quot.mk` / `Quotient.mk` / `Quotient.mk'`: the atom is
labeled `⟦·⟧`, typed by the quotient type's head name, and the underlying
representative is walked as a child via a `repr` relation. The equivalence-class
view (multiple representatives grouped) is a stretch goal, deferred.

### #21 — Indices of indexed inductive families — **DONE (this PR)**

**Decision: surface indices in the atom label; keep `type` stable.**
When a constructor's inductive has `numIndices > 0`, we read the index
expressions off the value's *type* (the trailing `numIndices` arguments) and
append them to the label: `cons : Vec 2`. The `type` field stays the head
constant's short name, so existing selectors are unaffected. The synthetic
`__index_n` relation and spec-projected variants from the issue are rejected:
indices are type-level data, and edges to them would suggest runtime structure
that isn't there.

### #13 — Structural decomposition of function bodies — **DONE (this PR)**

**Decision: structural decomposition only where today we show a leaf.**
Finite-domain enumeration (the #6 behavior) remains the default for enumerable
domains — extensional view first. For *non-finite* domains, where today the
lambda is an opaque labeled node, we enter the binder (`withLocalDecl`),
`whnfCore` the body, and decompose:

- `ite` / `dite` → node labeled `if`, edges `condition` / `then` / `else`
- `T.casesOn` applications → node labeled `match`, edge `match` to the
  discriminant, one edge per branch labeled by constructor name
- `Expr.letE` → edges `let_value` / `let_body`
- nested lambdas → recurse (multi-argument functions)

Anything else falls back to the current leaf label. A spec flag to force one
view or the other is deferred until someone asks for it.

### #8 — Finite type enumeration — **DONE (this PR)**

**Decision: `#spytial.enumerate <Type>` command, no `Fintype`, no `#spytial.map`.**
The issue proposes `[Fintype α]`, but `Fintype` is Mathlib — violates
principle 2. We already have `tryEnumerateDomain` (Bool, `Fin n` for n ≤ 20,
zero-arity enum inductives); the new command elaborates its argument as a type,
enumerates the inhabitants, and walks them all into a single shared diagram
(so a function field pointing at an enumerated element unifies with it).
`#spytial.map f` is unnecessary: `#spytial f` already enumerates finite
domains via the lambda arm — the demo shows this. Non-enumerable types get a
clear error naming what is supported.

### #2 — Spec lookup for parent-child relationships — **PARTIAL (this PR)**

**Decision: type classes work through the existing structure path; verify and
demo it; defer the rest.** Lean 4 classes *are* structures, so
`lookupTypeSpec`'s parent-chain walk already covers `class B extends A`.
This PR adds a demo proving it (spec on a parent class applies to a child
class instance). Deferred with rationale:

- *Explicit `spytial_spec RBNode extends Tree`*: new syntax for a niche need;
  wait for demand.
- *Per-instantiation specs (`List Nat` vs `List`)*: the spec store is keyed by
  `Name`; keying by type expression is a storage-format migration. Follow-up.
- *Subtype inheritance*: `{x : Nat // x > 0}` is headed by `Subtype`, and
  values are `Subtype.mk` pairs — inheriting the base type's spec silently
  would mislabel the wrapper atom. Needs its own design.

Issue stays open for the deferred cases.

### #24 — Notation-aware atom labels — **DONE (this PR)**

**Decision: route 1, per-spec opt-in via a new `.notationLabel` op.**
New op `.notationLabel (selector := "<TypeHeadName>")`. It is neither a
constraint nor a directive: per principle 4 it never reaches the YAML.
`#spytial`'s elaborator partitions it into `WalkConfig.collapseTypes`; when the
walker reaches an expression whose type-head short name matches, it emits a
single atom labeled with the *pre-whnf* pretty-printed expression (the
delaborator restores `[1, 2, 3]`, `(a, b)`, `a + b`) and does not decompose.
Limitation, documented: works in `with [...]` blocks only. Type-attached specs
(`spytial_spec`) store YAML, so relationalizer-side ops can't round-trip
through them until the storage format carries structured ops — follow-up.

### #23 — Term-size limits — **DONE (this PR)**

**Decision: measure, document, and add a `maxAtoms` guard.**
`WalkConfig.maxAtoms : Nat := 5000`; exceeding it throws a clear error rather
than hanging the editor. Benchmarks (relationalize time for `List.range N`,
a deep RBNode, a proof term) are recorded in the README "Performance and
limits" section with measured numbers and soft guidance.

### #10 — Proof-state visualization (`spytial_goals`) — **DONE (this PR)**

**Decision: ship the basic tactic, mark it experimental.**
`spytial_goals` walks the local context and goals of the current proof state:

- Hypotheses whose type is a const-headed Prop application `R a b …` become
  tuples in a relation named `R` (data args walked as atoms, proof args
  skipped).
- Data-typed hypotheses are relationalized normally.
- Goals get the same treatment, but their relations are prefixed `⊢ ` so specs
  can style hypothesis vs. goal differently.

Tactic diff (before/after), dependency highlighting, and interactivity are
stretch goals and stay in the issue.

### #20 — Mathlib smoke-test demo — **DEFERRED**

**Decision: separate project, separate PR.** Even an optional `lean_lib` in
this lakefile would force Mathlib onto every `lake update` resolution and CI
run (multi-GB artifacts). The right shape is a standalone `demos-mathlib/`
lake project that `require`s both spytial-lean and Mathlib, exercised manually
or in a dedicated CI job with `lake exe cache get`. It also genuinely needs a
human looking at the rendered output (screenshots in the PR), which is the
point of the issue. Stays open.

## Execution notes

- Agents work sequentially on one checkout (lake builds can't safely run
  concurrently in one dir); each change is verified with `lake build`
  (library + demos) before commit.
- Every feature lands with a demo file registered in the `Demos` lib roots in
  `lakefile.lean`.

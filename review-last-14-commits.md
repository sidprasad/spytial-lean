# Code review — findings

Review of the most recent 14 commits (`HEAD~14..HEAD`) on branch `owen`, covering the
selector DSL, the command/spec/attribute surface, the build-time coverage check, the
relationalizer + module-system migration, and the widget/build/CI infrastructure.

Every finding below was **reproduced on Lean `v4.32.0`** with the widget built, except where
explicitly marked *(static)*. Each is self-contained: symptom, location, a minimal
reproduction, and a suggested fix.

Severity key: **Major** = silent wrong result / false confidence in a guarantee the feature
exists to provide. **Moderate** = confirmed wrong result with a narrower trigger.
**Minor** = correctness-adjacent papercut, cosmetic, or docs.

---

## Major

### 1. `#spytial.coverage!` passes on a root namespace that matches nothing
**Where:** `SpytialLean/Coverage.lean:86` (`let root := stx[2].getId`), `:46` (prefix filter),
`:92` (`if uncovered.isEmpty`), `:101` (`if strict then throwError`).

**What happens:** the root-namespace argument is taken verbatim and never resolved or checked
to name an existing namespace. Candidates are filtered by `root.isPrefixOf n`. If the root
matches zero names, the report is empty, so `uncovered.isEmpty` is true and control takes the
`logInfo "0/0 … covered"` branch — the `throwError` is unreachable when `total = 0`. So even
the strict `!` form exits 0. A mistyped, renamed, or unimported root in a CI gate reports
success while nothing is checked.

**Reproduce:**
```lean
import SpytialLean
namespace Adv
structure Foo where x : Nat        -- has no spec → a real gap
end Adv
#spytial.coverage! Adv             -- error, exit 1  (correct)
#spytial.coverage! Ad              -- "0/0 … covered", exit 0  (bug: one-char typo passes)
#spytial.coverage! DoesNotExist    -- "0/0 … covered", exit 0
```

**Fix:** make strict mode fail (or at least warn) when `total = 0`, and/or resolve the root as
a namespace and error if it names nothing.

---

### 2. `#spytial.coverage!` fails the build for a structure that renders via an inherited spec
**Where:** `SpytialLean/Command.lean:335-352` (`lookupTypeSpec`) vs `SpytialLean/Coverage.lean:54-55`.

**What happens:** rendering composes a structure's spec with its parents' specs down the
`getAllParentStructures` chain, so `Child extends Parent` with no own spec renders using the
parent's spec. But `coverageReport` marks a type covered only on a **direct** registration hit
(`getSpytialSpec?`/`getSpytialOptOut?`/`getSpytialRelationalizerName?` on that exact name) — it
never walks the parent chain. So strict coverage throws for a child that visualizes correctly.
(This is the pattern documented in `demos/Showcase.lean:96-109`: `Car extends Vehicle`,
"inherits Vehicle's spec automatically".) Currently latent — no shipped build target runs strict
coverage over an `extends` type — but the behavior is a live contradiction of the inheritance feature.

**Reproduce:**
```lean
import SpytialLean
namespace Adv
structure Parent where a : Nat
spytial_spec Parent [ hideField a ]
structure Child extends Parent where b : Nat   -- no own spec
end Adv
-- #spytial (c : Adv.Child) renders using Parent's spec (lookupTypeSpec returns the parent ops)
#spytial.coverage! Adv                          -- error: "Adv.Child uncovered", exit 1
```

**Fix:** in `coverageReport`, treat a type as covered when it has a direct registration **or** any
ancestor supplies a spec (mirror `lookupTypeSpec`'s parent walk).

---

### 3. Dotted-join arity is mis-scored, so the "checked" selector DSL accepts an arity-invalid selector
**Where:** `SpytialLean/SelectorElab.lean:616` (`joinRest`) vs `:629` (`resolveHead`);
`group` registers arity 1 at `SpytialLean/Command.lean:230`.

**What happens:** in a dotted identifier join `X.y`, `joinRest` checks `scope.introduced.contains`
but then passes the **literal `(some 2)`** as `y`'s arity instead of looking up its real arity the
way `resolveHead` does with `scope.introduced.get?`. A spec-introduced `group` has arity 1, so
`X.group` is computed as `1 + 2 − 2 = 1` and accepted by a unary op, even though a join of two
arity-1 sets has arity 0 ("no columns left"). The spaced spelling of the same operator goes
through a different path and rejects it correctly — so the two spellings disagree.

**Reproduce:** (declare `SBDD` + a `group` mirroring `tests/SelectorTest.lean`)
```lean
spytial_spec SBDD [ group SBDD cluster, hideAtom SBDD.cluster ]     -- accepted, exit 0  (bug)
spytial_spec SBDD [ group SBDD cluster, hideAtom SBDD . cluster ]   -- error: "join of arity 1
                                                                    -- and arity 1 has no columns left"
```

**Fix:** in `joinRest`, look up the component's real arity (`scope.introduced.get?` /
`scope.rels.get?`) instead of hardcoding `2`.

---

### 4. A qualified (multi-component) type name in a selector is rejected, though the code claims to support it
**Where:** `SpytialLean/SelectorElab.lean:609`, `:630-633` (the comment at `:630` claims
`Cslib.SKI`-style multi-component type refs are supported). Same `joinRest` root cause as #3.

**What happens:** `hideAtom A.T`, where `A.T` is a qualified **type** name (not opened), resolves the
whole dotted identifier as a type sig but then still folds the tail component `T` as a relation join,
which fails with `unknown relation 'T'`. Users cannot hide/style a namespaced type by its qualified
name — relevant because the intended target corpus (Cslib) is namespaced. A bare/opened name works.

**Reproduce:**
```lean
-- with a type A.T in scope:
spytial_spec Container [ hideAtom A.T ]          -- error: unknown relation 'T' (did you mean 'T'?)
spytial_spec Container [ open A in hideAtom T ]  -- works (workaround)
```

**Fix:** handle multi-component type references in the join/resolution path (same area as #3);
if `A.T` resolves to a type, don't re-interpret the trailing component as a relation.

---

### 5. `just demos` (and every CI path) never elaborates 3 of the 8 demos
**Where:** `lakefile.lean:80-83` (`Demos.roots`); claim contradicted at `DEVGUIDE.md:55-61`.

**What happens:** the `Demos` lib lists only 5 roots (`Showcase`, `ProofFieldFiltering`,
`FunctionFields`, `TypeClassInstances`, `CustomRelationalizer`) with no `globs`, so Lake builds only
those plus their imports. `demos/HoareLogic.lean`, `demos/OperationalSemantics.lean`, and
`demos/ProofTerms.lean` — **13 `#spytial` sites** — are never elaborated by `just demos`. No other
target reaches them either: bare `lake build` builds only `@[default_target] SpytialLean`, and
`just test` builds `SpytialTests`. DEVGUIDE states `just demos` elaborates "every demo — each
`#spytial` site typechecks and its spec elaborates." A regression in those 3 files ships green.
(All 3 currently elaborate standalone, so this is unchecked-but-valid coverage, not a latent break.)

**Fix:** add the 3 files to `Demos.roots` (or switch to a submodule glob over `demos/`), and/or
soften the DEVGUIDE wording.

---

## Moderate

### 6. Custom relationalizer + a repeated value → a tuple referencing a non-existent atom
**Where:** `SpytialLean/Relationalizer.lean:160-170`.

**What happens:** `walkExpr` allocates an `atomId` and records `seen[hash] := atomId` **before**
dispatching to a custom relationalizer, and never writes back the id the relationalizer actually
returns (the demo returns its own `graphId`, not `atomId`). The pre-allocated id is never emitted.
If the same value appears twice and its type has a custom relationalizer, the second (memoized)
occurrence resolves to that orphaned id, producing a tuple that references an atom absent from the
`atoms` array. `toDataInstance` does no pruning, so the malformed payload reaches the widget.

**Reproduce:** using the `demos/CustomRelationalizer.lean` `SimpleGraph` relationalizer,
`#spytial (p : SimpleGraph × SimpleGraph := (g, g))` emits a `snd` tuple `[atom_0, atom_1]` where
`atom_1` is not among the emitted atoms.

**Fix:** after custom dispatch, reconcile `seen[hash]` to the id the relationalizer returned (or
don't pre-allocate/`markSeen` on the custom-relationalizer branch).

---

### 7. A non-`public` custom relationalizer registers and counts as covered but fails to render across modules
**Where:** `SpytialLean/Relationalizer.lean:88-95` (evaluation via `Meta.evalExpr … (mkConst declName)`),
`SpytialLean/Command.lean:435-446` (registration typechecks but does not require `public`);
pattern modeled at `tests/CoverageTest.lean:33`.

**What happens:** registering a non-`public` (`meta def`) relationalizer succeeds, and the coverage
check counts the type as covered (the registration is present). But under the module system the
declaration is name-mangled to `_private.<module>.…`, which an importing module cannot access, so a
`#spytial` on a value of that type **from another module** fails at evaluation with
`Unknown constant '_private.…'`. The repo's own test uses a non-`public meta def` relationalizer, but
only ever runs same-file coverage (which checks registration presence), so this gap is neither
exercised nor caught in-repo. Net: a type can report "covered" yet be unrenderable by downstream
importers. *(Note: a `public meta def` relationalizer works cross-module; a plain non-`meta` `def`
of the relationalizer type is rejected by Lean at definition time, so `public meta def` is the
correct pattern.)*

**Reproduce:** module `A` with `meta def boxRel : CustomRelationalizer := …` (no `public`) +
`spytial_relationalizer Box boxRel`; import `A` from module `B` and run `#spytial (Box.mk 42)`
→ `error: Unknown constant '_private.A.0.boxRel'`. Making `boxRel` `public` fixes it.

**Fix:** have `spytial_relationalizer` warn or error when the registered declaration is not
`public` (it is unusable across module boundaries), and use `public meta def` in the docs/tests.

---

### 8. Derived type/field names are not injective; type-scoped selectors over-match
**Where:** `SpytialLean/TypeShape.lean:12-16` (`shortName` drops namespace qualifiers),
`:44-49` (`fieldRelName` uses the bare binder), merge at `SpytialLean/Relationalizer.lean:30-33`.

**What happens:** distinct types `A.T` and `B.T` both emit atom `type := "T"`, and two different
constructors that each have a field `left` emit the same relation name `"left"` (merged into one
relation). `hideAtom T` / `hideField left` then match both. Atom ids stay distinct, so graph
topology is preserved — the effect is over-broad styling/hiding, not lost structure. This is the
short-name convention shared with the Rust/Python Spytial implementations, so it's largely
intentional; the sharp edge is that the **checker** resolves `T` to one specific declaration (and
shows it on hover) while the **runtime** selector matches every type with that short name.

**Reproduce:** two structures `A.T`/`B.T` (or `inductive Two | foo (left:Nat) | bar (left:Nat)`),
relationalize a value containing both, and the payload shows one `"T"` type / one `"left"` relation
carrying both types' tuples.

**Fix (if desired):** qualify names on collision, or document the convention and the checker/runtime
scope difference explicitly.

---

## Minor

### 9. Coverage silently ignores private / non-`public` data types
`SpytialLean/Coverage.lean:46` — candidates are filtered by `!n.isInternalDetail && root.isPrefixOf n`.
Under the module system a `private`/non-`public` structure is name-mangled to `_private.…`, which is
both an internal detail and fails the prefix test, so it is never counted (a blind spot, not a false
"covered"). *Reproduced: a namespace whose only type is `private structure` passes `#spytial.coverage!`
as `0/0`.*

### 10. The non-strict `#spytial.coverage` cannot fail a build
`SpytialLean/Coverage.lean:101` emits `logWarning` (not `throwError`) on a gap, and there is no
`warningAsError` / `-DwarningAsError` anywhere in `lakefile.lean`, `.github/workflows/build.yml`, or
`justfile`. Only the `!` form enforces anything; the plainer-looking default is inert as a gate.

### 11. Coverage tests never pin the "can't false-pass" property
`tests/CoverageTest.lean` asserts the warning path, the strict-error path, and a non-strict clean
pass, but never runs strict `!` on a fully-covered namespace and never tests an empty/nonexistent
namespace — so findings #1 and (a strict clean pass) are unguarded against regression. *(static)*

### 12. The `flag` op name is emitted unquoted and unvalidated
`SpytialLean/Command.lean:291` takes the name as `(← a.ident 0 …).getId.toString` with no
validation, and `SpytialLean/Spec.lean:148-149` renders `s!"  - flag: {name}"` — the only string
field not routed through the `q` quoting helper. `flag true` yields `flag: true`, which parses as a
YAML **boolean**, not the string; `flag «a: b»` puts a `: ` in a plain scalar and breaks parsing of
the whole directives block. Note a golden test pins the bare form `flag: hideDisconnected`, so the
fix is *quote-when-needed* (or validate the name to a safe identifier), not always-quote.

### 13. `q` does not escape newlines
`SpytialLean/Spec.lean:95-101` escapes only `"` and `\`. A string argument (or `.raw` selector)
containing `\n` — e.g. `atomColor B "a\nb"` — emits a literal newline inside a single-line flow
scalar, which YAML folds to a space, silently changing the value to `"a b"`. (Tabs are also
unescaped but round-trip correctly, so newlines are the actual corruption vector.)

### 14. `ni` lowers to a semantically different constraint, guarded only by a warning
`SpytialLean/SelectorElab.lean:758-764` (lowering `SpytialLean/Selector.lean:272`) emits `ni`
verbatim to SGQ with a compile-time warning noting the engine computes `¬(a in b)` while Forge
defines `a ni b ≡ b in a` (these are not equivalent). If the warning is ignored, the rendered
constraint silently means something other than intended. Consider rewriting `a ni b` to the
Forge-equivalent `b in a` at lowering rather than relying on the warning.

### 15. Empty box-join `e[]` silently becomes `e`
`SpytialLean/SelectorElab.lean:196` uses `sepBy` (not `sepBy1`) and the join loop (`:488-497`) no-ops
on empty arguments, so `orientation lo[] below` is byte-identical to `orientation lo below` with no
diagnostic. A typo degrades silently. Consider `sepBy1` or rejecting empty argument lists.

### 16. Dead `SelVal.boolLit` / half-wired `@bool:` literal
`SpytialLean/Selector.lean:127` declares `boolLit` and `:264`/`:317` consume it, but no surface
syntax ever produces it (`@bool:` is a label projection, not a literal). Either wire a `true`/`false`
literal or drop the constructor. *(static)*

### 17. Two imprecise diagnostics
`SpytialLean/SelectorElab.lean:673-675`: `@:x = 5` reports "cannot compare a label value with a
relational expression" though `5` is an integer. `:530`: a **quantifier** binder-domain arity error
hardcodes the phrase "comprehension binder domain" (the helper is shared with comprehensions).

### 18. Compiled-relationalizer cache is stale after an interactive body edit
`SpytialLean/Relationalizer.lean:84-95` — a process-lifetime `IO.Ref` keyed by declaration name with
no invalidation. Editing a relationalizer's body (same name) in the same editor worker keeps the old
compiled closure, so `#spytial` renders the previous version. Harmless under `lake build`/CLI (fresh
process); it bites the interactive "iterate on a relationalizer" loop. Consider keying by body hash
or clearing on environment change.

### 19. The widget bundle guard checks existence but not content
`widget/rollup.virtual.mjs:12-16` throws if the `spytial-core` bundle file is missing but not if it
is present-and-empty/truncated, which would embed an empty module silently. Effectively unreachable
for a registry install (content-addressed store + integrity + `--frozen-lockfile`); only semi-plausible
with a local `file:` checkout mid-build. Add a non-empty check if you support local core checkouts.

### 20. README omits pnpm from build-from-source prerequisites
`README.md:30-32` lists only "Node.js" and `:45` says "elan + Node + just", but `lake build` shells
`pnpm install --frozen-lockfile`, and Node does not put `pnpm` on `PATH` (needs corepack). The Nix
shell already provides pnpm and `DEVGUIDE.md:19` lists it — just add pnpm to the README prerequisites.

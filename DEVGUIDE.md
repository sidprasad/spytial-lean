# Development Guide

## Architecture overview

spytial-lean has two build systems that feed into each other:

1. **Widget JS** (pnpm + rollup) — compiles `widget/src/spytialWidget.tsx` into a single JS file at `.lake/build/js/spytialWidget.js`
2. **Lean** (lake) — compiles the Lean library, embedding the widget JS via `include_str`

The Lean build depends on the widget JS through the `widgetJsAll` lake target,
which runs `pnpm install --frozen-lockfile` and `pnpm run build` in `widget/`
whenever its tracked inputs (sources, rollup configs, `package.json`,
`pnpm-lock.yaml`) change. The lockfile is committed; dependency changes go
through `pnpm add` / `pnpm remove` in `widget/`.

The widget's spytial-core dependency is declared in
[`widget/package.json`](widget/package.json) and pinned in `pnpm-lock.yaml`.
Core preserves relations by `id`; selectors
resolve a `name` to the set union of all records with that name. Lean stores
relations by ID and emits structural field IDs qualified by the exposed owner
type. Observations and checked facts use the full constant name or unique local
head identity plus retained column types. Same-named fields, observations, and
facts therefore coexist without losing tuples or changing selector spelling.

Reification selects the structural field ID determined by the owner's type and
field name. A same-named observation cannot supply a missing field or corrupt an
existing one. Custom relationalizers can pass an explicit `id` to
`WalkState.addTuple` / `addRelation`; display names stay separate.

`ReconstructionInvariance` makes that separation a theorem. `JsonDataInstance.SameStructure`
compares atoms and the tuples selected by structural field IDs, ignoring relation
names and relation-level metadata. `Structural.reify_relationalize_of_sameStructure`
preserves the unchecked round trip for a `LosslessIdentity` value after any change
preserving this view and the root. Its corollaries allow arbitrary relation
renaming and appending relations with nonstructural IDs, with atoms fixed.
No uniqueness requirement on display names enters these proofs.

## Context inspection

[Evidence and context preparation](docs/evidence.md) describes the preparation,
normalization, proof-export, and interpretation boundaries shared by functions and
theorems. Whole-value commands keep the structural computation path.

## Structural reconstruction

Reconstruction is described by capabilities and their laws:

| Capability | Guarantee |
| --- | --- |
| `SpytialReify α` | A decoder for values of `α`. |
| `StructuralReification α` | An independent structural checker whose success implies decoding. |
| `StructuralExposure α` | A typed exposure into the shared walker, with proofs connecting it to that checker. |
| `LosslessIdentity α` | The selected sharing policy preserves the full structure of every value of `α`. |

`deriving SpytialReify` supplies the first three together for supported datatypes.
`deriving LosslessIdentity` proves the sharing law for a concrete type; for a
parameterized type, use `instance : LosslessIdentity (T ...) := by spytial_lossless`.
`Structural.reify_relationalize_of_lossless` then proves
`reify (Structural.relationalizeCandidate value) = Except.ok value` for every value.

Automatic deriving supports regular first-order, non-indexed inductive types and
structures, including explicit, implicit, strict-implicit, and instance-implicit
data fields. Hidden fields are decoded from their relations and passed explicitly
to the constructor; an available default instance cannot replace a stored field.
The current handler requires distinct field-relation names within a constructor
and does not yet derive dependent/indexed families, mutual or nested recursion,
or proof-, type-, or function-valued fields. These are deriving limitations;
additional types can supply matching instances and proofs directly.

## Prerequisites

- Lean 4 (pinned by `lean-toolchain`, installed via [elan](https://github.com/leanprover/elan))
- Node.js + [pnpm](https://pnpm.io/)
- [just](https://github.com/casey/just) (optional)

Run `nix develop` for a shell with these tools. To load it with direnv, run
`ln -s nix/envrc .envrc` and `direnv allow` from the repository root.

## Tasks

### Build

Build the widget JS and Lean library with `just build`, or directly with lake:

```sh
lake build
```

The first build also fetches the Lean dependencies (Aesop, Batteries, and
ProofWidgets4) pinned in `lake-manifest.json`. Under the hood `just build` runs `pnpm install
--frozen-lockfile` and `pnpm run build` in `widget/` before compiling Lean.

### Tests

Run the headless unit tests (relationalizer naming, selector checking, coverage
checking) with `just test`, or directly with lake:

```sh
lake build SpytialTests
```

`SpytialTests/SelectorTest.lean` is the behavioral contract for the selector DSL. It
pins the SGQ lowering of every surface form: the Forge precedence battery,
word and symbolic connectives, quantifiers and `let`, the integer layer, box
join, and the negated comparisons. It also pins one diagnostic per checker
error class.

After building the tests, `node render/infoview-test.mjs --rpc-only` checks the
widget payloads served by Lean, including proof edits and tactic backtracking.
Build `renderHarnessJs` and run the same script without the flag to exercise
the interactions in Playwright Chromium as well.

### Demos

Elaborate every demo — each `#spytial` site typechecks and its spec elaborates —
with `just demos`, or directly with lake:

```sh
lake build Demos
```

### Snapshot renders

`#spytial_snapshot` dumps widget props from any Lean file; a pinned container
renders the dumps to PNGs. See `render/README.md`.

### Widget reload

The built JS's hash is part of the `widgetJsAll` trace, so `just build`
re-embeds it whenever its bytes change. Lake still only reruns the widget build
when a tracked input changes — after rebuilding a local spytial-core checkout
(below), rebuild and re-embed with:

```sh
just widget-reload
```

Either way, restart the Lean server (VS Code: **Cmd+Shift+P → "Lean 4: Restart
Server"**) to pick up the new widget.

### Changed spytial-core

spytial-core is a registry dependency (`spytial-core` in `widget/package.json`).
Bump the version and run `pnpm install` in `widget/`; the next `just build`
re-embeds it. For an unreleased core, point the dependency at a local checkout
(`"spytial-core": "file:../../spytial-core"`) and use `just widget-reload`
after each core rebuild.

## Widget build details

### How spytial-core is bundled

`widget/src/spytialWidget.tsx` selects the inspection and arranges the explorer
panes. `diagramLayout.ts` evaluates the Lean payload with `spytial-core`. Each
`DiagramWidget.tsx` owns one graph element and renders its diagnostics with
`ErrorMessageModal` from `spytial-core/react`.

Rollup bundles these ES modules and inlines their dynamic imports so Lean can
serve the widget as one file. The infoview supplies React. The standalone
render harness bundles React as well. Both use the VS Code theme rules in
`widget/src/widgetStyles.ts`.

### Build output

```
widget/src/spytialWidget.tsx
  → (tsc)    widget/dist/spytialWidget.js
  → (rollup) .lake/build/js/spytialWidget.js
```

The final `.lake/build/js/spytialWidget.js` is what `include_str` embeds into
the Lean `@[widget_module]`.

## Adding a new SpytialOp

There is nothing to add here. The op surface is derived from spytial-core's
`docs/spytial-language.json` while `SpytialLean/SpecLang.lean` elaborates, and
the selector grammar from simple-graph-query's `docs/sgq-language.json` in
`SpytialLean/Sgq.lean`; the op elaborator in `SpytialLean/OpElab.lean`, the serializer and the usage
strings read those tables. A new item or field lands by bumping the dependency and
rebuilding, and a shape the tables cannot represent fails that build naming
the item. What stays hand-written — the Lean-side spelling choices and the
facts the manifest does not carry yet — is listed in
[docs/language-manifests.md](docs/language-manifests.md). Pin new surface in
`SpytialTests/SpecSurfaceTest.lean` and show it in a `Demos/` file.

## Debugging

### Inspect relationalizer output

```lean
#spytial.datum myValue
```

Shows the JSON data instance: atoms and relations with their names. The spec
elaborator checks selector names against the same vocabulary.

### Inspect the generated spec

```lean
#spytial.spec myValue with [orientation left below]
```

Shows the spec string that gets passed to `parseLayoutSpec`.

### Widget console errors

In VS Code, open the Developer Tools (**Help → Toggle Developer Tools**) and check the Console tab for `SpytialWidget render error` messages.

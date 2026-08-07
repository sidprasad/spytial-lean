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

## Prerequisites

- Lean 4 (pinned by `lean-toolchain`, installed via [elan](https://github.com/leanprover/elan))
- Node.js + [pnpm](https://pnpm.io/)
- [just](https://github.com/casey/just) (optional)

The nix dev shell (`flake.nix`) provides all of these; see the
[README](README.md#nix-dev-shell) for direnv setup.

## Tasks

### Build

Build the widget JS and Lean library with `just build`, or directly with lake:

```sh
lake build
```

The first build also fetches the Lean dependencies (ProofWidgets4) pinned in
`lake-manifest.json`. Under the hood `just build` runs `pnpm install
--frozen-lockfile` and `pnpm run build` in `widget/` before compiling Lean.

### Tests

Run the headless unit tests (relationalizer naming, coverage checking) with
`just test`, or directly with lake:

```sh
lake build SpytialTests
```

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
Bump the version there, update the `minimumReleaseAgeExclude` pin in
`pnpm-workspace.yaml` to match, and run `pnpm install` at the workspace root;
the next `just build` re-embeds it. For an unreleased core, point the
dependency at a local checkout
(`"spytial-core": "file:../../spytial-core"`) and use `just widget-reload`
after each core rebuild.

After bumping, regenerate the authoring surface and commit the diff:

```sh
just gen-spec
```

`SpytialLean/SpecGenerated.lean` (the `SpytialOp` constructors, enums, style
blocks, YAML serialization, and validation) is generated from the language
manifest the npm package ships at
`widget/node_modules/spytial-core/docs/spytial-language.json` — the same
release the workspace lockfile pins for the renderer, so the two cannot drift
apart. `just check-spec` fails when the checked-in file is stale, and CI runs
it. The generator (`codegen/SpecCodegen.lean`) hard-errors on any manifest
construct it wasn't written for, so a core release that grows the language
stops codegen by name; deliberate divergences live in the override tables at
the top of the generator, each with its reason.

## Widget build details

### How spytial-core is bundled

The widget can't load external scripts (VS Code webview CSP blocks CDN), and
spytial-core ships as IIFE bundles. `widget/rollup.virtual.mjs` wraps the two
pre-built bundles from `node_modules/spytial-core/dist/` in virtual modules,
which `rollup.config.js` pulls in via `cssNoop()` / `spytialCoreVirtualModules()`:

- `spytial-core` — the layout engine (`spytial-core-complete.global.js`), with
  `customElements.define` guarded against duplicate registration
- `spytial-core-components` — the error modal / error-state manager
  (`react-component-integration.global.js`)

so `spytialWidget.tsx` imports them like ordinary modules. CSS imports from
spytial-core are handled by a `css-noop` plugin (the import becomes a no-op);
equivalent styles are injected at runtime by the widget itself.

The engine bundle includes all of spytial-core's dependencies (d3, webcola,
dagre, etc.) — this is why the final widget JS is ~3MB.

### Build output

```
widget/src/spytialWidget.tsx
  → (tsc)    widget/dist/spytialWidget.js
  → (rollup) .lake/build/js/spytialWidget.js
```

The final `.lake/build/js/spytialWidget.js` is what `include_str` embeds into
the Lean `@[widget_module]`.

## Adding a new SpytialOp

`SpytialOp` is generated — new operations come from spytial-core's language
manifest, not from hand-edits. When a core release adds one, `just gen-spec`
picks it up (or hard-errors naming the construct if the generator needs
teaching — extend the override tables in `codegen/SpecCodegen.lean`). Then
add an example in `demos/Showcase.lean` and rebuild: `lake build Demos`.

## Debugging

### Inspect relationalizer output

```lean
#spytial.datum myValue
```

Shows the JSON data instance — atoms and relations with their names. Use this to find the correct selector strings for your spec.

### Inspect generated YAML

```lean
#spytial.spec myValue with [.orientation (selector := "left") (directions := [.below])]
```

Shows the YAML that gets passed to `parseLayoutSpec`.

### Widget console errors

In VS Code, open the Developer Tools (**Help → Toggle Developer Tools**) and check the Console tab for `SpytialWidget render error` messages.

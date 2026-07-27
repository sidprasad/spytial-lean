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

Run the headless unit tests (relationalizer naming, selector checking, coverage
checking) with `just test`, or directly with lake:

```sh
lake build SpytialTests
```

`tests/SelectorTest.lean` is the behavioral contract for the selector DSL: it
pins the SGQ lowering (compiled JSON) of every surface form — the Forge
precedence battery, word/symbolic connectives, quantifiers and `let`, the
integer layer, box join, negated comparisons (`!in`, `not in`, `ni`, `!ni`) —
plus one diagnostic per checker error class and a warning golden for each
engine-bug form (`<:`, `:>`, `++`, arrow-multiplicity, backquote, `sum[e]`).

### Demos

Elaborate every demo — each `#spytial` site typechecks and its spec elaborates —
with `just demos`, or directly with lake:

```sh
lake build Demos
```

### Render tests

Image-snapshot tests of the widget in headless Chrome: each case in
`tests/render/Cases.lean` dumps the real widget props, a rollup harness mounts
the same compiled component on them, and Playwright pixel-compares a screenshot
against `tests/render/baseline/`. See
[tests/render/README.md](tests/render/README.md).

```sh
just render            # full suite (`just render -g rbtree` filters by case)
just render-update     # re-bless baselines — inspect the PNGs first!
just render-review     # kitty terminals: re-blessed baselines vs HEAD, side by side
```

Requirements: a host Chrome — Playwright's downloaded browsers don't run on
NixOS, so the config uses `google-chrome-stable` from PATH (`SPYTIAL_CHROME`
overrides) — and no strict sandbox (Chrome needs unix sockets).

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
  → (tsc)    widget/dist/spytialWidget.js      ← render harness mounts this
  → (rollup) .lake/build/js/spytialWidget.js   ← include_str embeds this
```

The final `.lake/build/js/spytialWidget.js` is what `include_str` embeds into
the Lean `@[widget_module]`.

## Adding a new SpytialOp

To add a new layout operation:

1. Add the constructor to `SpytialOp` in `SpytialLean/Spec.lean`
2. Add it to `isConstraint` (if it's a constraint) or leave it as a directive
3. Add a JSON serialization case in `SpytialOp.toJson` (in `SpytialLean/Spec.lean`)
4. Add a keyword case to `elabSpytialOp` in `SpytialLean/Command.lean`, giving each selector position its `ArityExpect` and interpreting the other arguments
5. Add an example in a `demos/` file and a golden in `tests/SelectorTest.lean`
6. Rebuild: `lake build Demos SpytialTests`

## Debugging

### Inspect relationalizer output

```lean
#spytial.datum myValue
```

Shows the JSON data instance — atoms and relations with their names. The spec
elaborator checks selector names against the same vocabulary, so this is for
seeing the data, not for guessing names.

### Inspect the generated spec

```lean
#spytial.spec myValue with [orientation left below]
```

Shows the spec string (JSON, which is valid YAML) that gets passed to
`parseLayoutSpec`.

### Widget console errors

In VS Code, open the Developer Tools (**Help → Toggle Developer Tools**) and
check the Console tab for `SpytialWidget render error` messages. Outside VS
Code, `just render` surfaces the same component's errors headlessly (widget
error state and `constraint-error` events fail the test).

# Development Guide

## Architecture overview

spytial-lean has two build systems that feed into each other:

1. **Widget JS** (npm + rollup) — compiles `widget/src/spytialWidget.tsx` into a single JS file at `.lake/build/js/spytialWidget.js`
2. **Lean** (lake) — compiles the Lean library, embedding the widget JS via `include_str`

The Lean build depends on the widget JS build through the `widgetJsAll` lake target.

## Prerequisites

- Lean 4 (pinned by `lean-toolchain`, installed via [elan](https://github.com/leanprover/elan))
- Node.js (v16+)
- spytial-core browser bundle built: `cd ../spytial-core && npm run build:browser`
- [just](https://github.com/casey/just) (optional)

The nix dev shell (`flake.nix`) provides the toolchain; see the
[README](README.md#nix-dev-shell) for direnv setup.

## Tasks

### Build

Build the widget JS and Lean library with `just build`, or directly with lake:

```sh
lake build
```

The first build also fetches the Lean dependencies (ProofWidgets4) pinned in
`lake-manifest.json`. Under the hood `just build` runs `npm clean-install` and
`npm run build` in `widget/` before compiling Lean.

### Tests

Run the headless relationalizer-naming tests (TypeShape) with `just test`, or
directly with lake:

```sh
lake build SpytialTests
```

### Demos

Elaborate every demo — each `#spytial` site typechecks and its spec elaborates —
with `just demos`, or directly with lake:

```sh
lake build Demos
```

### Widget reload

Lake tracks the widget sources and configs, so `just build` picks up changes to
them. What it can't see is the spytial-core bundle, which rollup reads straight
from `../../spytial-core/dist/browser/` — after rebuilding that, force the
re-embed with:

```sh
just widget-reload
```

Either way, restart the Lean server (VS Code: **Cmd+Shift+P → "Lean 4: Restart
Server"**) to pick up the new widget.

### Changed spytial-core

To pick up changes to spytial-core itself, rebuild its browser bundle and reload
the widget:

```sh
cd ../spytial-core && npm run build:browser && cd ../spytial-lean
just widget-reload
```

## Widget build details

### How spytial-core is bundled

The widget can't load external scripts (VS Code webview CSP blocks CDN). Instead, the pre-built spytial-core IIFE bundle (`spytial-core/dist/browser/spytial-core-complete.global.js`) is embedded into the widget JS via a rollup virtual module:

```
rollup.config.js
  → reads the IIFE bundle from ../../spytial-core/dist/browser/
  → creates a virtual 'spytial-core' module that runs the IIFE and exports spytialcore
  → guards customElements.define to prevent duplicate registration errors
```

The IIFE bundle includes all of spytial-core's dependencies (d3, webcola, dagre, etc.) — this is why the final widget JS is ~3MB.

### Error components

The `ErrorMessageModal` and `ErrorStateManager` are imported directly from spytial-core's **source** (not from a pre-built bundle):

```
widget/src/spytialWidget.tsx
  → imports from ../../../spytial-core/src/components/ErrorMessageModal/
```

The CSS for these components is handled by a rollup `css-noop` plugin (the CSS import becomes a no-op), and equivalent styles are injected at runtime by the widget itself.

### Build output

```
widget/
  src/spytialWidget.tsx     → (tsc) → dist/spytialWidget.js → (rollup) → ../.lake/build/js/spytialWidget.js
```

The final `.lake/build/js/spytialWidget.js` is what `include_str` embeds into the Lean `@[widget_module]`.

## Adding a new SpytialOp

To add a new layout operation:

1. Add the constructor to `SpytialOp` in `SpytialLean/Spec.lean`
2. Add it to `isConstraint` (if it's a constraint) or leave it as a directive
3. Add a YAML serialization case in `constraintToYaml` or `directiveToYaml`
4. Add an example in `Demo.lean`
5. Rebuild: `lake build Demo`

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

# Development Guide

## Architecture overview

spytial-lean has two build systems that feed into each other:

1. **Widget JS** (npm + rollup) — compiles `widget/src/spytialWidget.tsx` into a single JS file at `.lake/build/js/spytialWidget.js`
2. **Lean** (lake) — compiles the Lean library, embedding the widget JS via `include_str`

The Lean build depends on the widget JS build through the `widgetJsAll` lake target.

## Prerequisites

- Lean 4 v4.24.0 (installed via [elan](https://github.com/leanprover/elan))
- Node.js (v16+)
- spytial-core browser bundle built: `cd ../spytial-core && npm run build:browser`

## Full build from scratch

```sh
cd spytial-lean

# 1. Fetch Lean dependencies (ProofWidgets4, batteries)
lake update

# 2. Build everything (widget JS + Lean)
lake build
```

`lake build` automatically runs `npm clean-install` and `npm run build` in the `widget/` directory before compiling Lean.

## Rebuilding after changes

### Changed Lean files only

```sh
lake build
```

### Changed widget TypeScript

The widget needs to be recompiled, and then Widget.lean needs to be recompiled (because `include_str` embeds the JS at compile time):

```sh
# Rebuild the widget JS
cd widget
npx tsc && npx rollup --environment NODE_ENV:production --config
cd ..

# Force Widget.lean to recompile with new JS
rm -f .lake/build/lib/lean/SpytialLean/Widget.*
lake build
```

Then in VS Code: **Cmd+Shift+P → "Lean 4: Restart Server"** to pick up the new widget.

### Changed spytial-core

If you modify spytial-core itself:

```sh
# Rebuild spytial-core's browser bundle
cd ../spytial-core
npm run build:browser
cd ../spytial-lean

# Rebuild widget (picks up new IIFE bundle)
cd widget
npx tsc && npx rollup --environment NODE_ENV:production --config
cd ..

# Force recompile
rm -f .lake/build/lib/lean/SpytialLean/Widget.*
lake build
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

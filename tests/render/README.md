# Render snapshot tests

Image-snapshot tests for the infoview widget: each case renders real widget
props in headless Chrome and pixel-compares a screenshot of the diagram
container against a committed baseline PNG. This is the only test layer that
sees actual layout — geometry, edge routing, colors, grouping — without
launching VS Code. The capture is the container element only: the toolbar's
native `<select>`s are the most machine-dependent paint on the page, and the
rest of the viewport is blank.

## Pipeline

```
tests/render/Cases.lean (#spytial_snapshot)
    │  lake env lean tests/render/Cases.lean
    ▼
cases/<name>/props.json          -- byte-identical to what savePanelWidgetInfo
    │                               hands the widget (spytialProps in Command.lean)
    │  lake build renderHarnessJs
    ▼
dist/harness.js                  -- entry.mjs + widget/dist/spytialWidget.js
    │                               + react + the spytial-core bundles
    │  render.spec.mjs (Playwright, host Chrome)
    ▼
baseline/<name>.png (committed)  +  out/<name>/{page.html,render.svg,metrics.json}
```

The harness mounts the same compiled component the infoview embeds, and both
rollup configs resolve spytial-core through `widget/rollup.virtual.mjs`, so a
pass here is evidence about the real infoview render, not a simulation.

## Running

```sh
just render              # full suite
just render -g rbtree    # one case (playwright title filter)
just render-update       # re-bless baselines — inspect the PNGs first!
just render-review       # kitty terminals: re-blessed baselines vs HEAD, side by side
```

Failures write actual/expected/diff PNGs under `out/test-results/` and a
visual report to `out/report/index.html`.

Requirements: a host Chrome (`SPYTIAL_CHROME` overrides the binary —
Playwright's downloaded browsers don't run on NixOS, hence system Chrome) and
no strict sandbox (Chrome needs unix sockets). Everything else comes from the
flake dev shell. The `node_modules` symlink into `widget/` is how the spec
files resolve `@playwright/test`.

## Adding a case

Add a line to `Cases.lean`:

```lean
#spytial_snapshot "my-case" myValue with [orientation next below]
```

then `just render-update` and commit the new `baseline/my-case.png` — after
looking at it.

## Settle protocol

The page (`entry.mjs`) is passive: it mounts the widget and records the graph
element's `layout-complete` / `constraint-error` CustomEvents on a document
capture listener. The spec polls for those from the node side — headless
Chrome throttles in-page timers (a settle `setInterval` in the page freezes
after a few fires), while CDP evaluates always run — and then leans on
`toHaveScreenshot`'s stabilization (two consecutive identical frames) for any
animation tail. Byte-stability of the SVG alone is *not* a settle signal: the
constraint solver pauses mid-layout long enough to fake it (baselines once
captured a "Computing layout... 8%" toast — the toast's visibility is now an
explicit assertion at settle, not a job for the pixel crop).

`metrics.json` per case records node centers/sizes/fills, edge lengths and
straightness (`straightness: null` = path never routed), and group boxes —
read back from the live SVG, for diagnosing drifts without opening the report.

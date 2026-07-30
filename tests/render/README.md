# Render snapshot tests

Image-snapshot tests for the infoview widget: each case renders real widget props
in headless Chromium and pixel-compares the diagram against a committed baseline.
This is the only test layer that sees actual layout — geometry, edge routing,
colors, grouping — without launching VS Code.

## Pipeline

```
Cases.lean (#spytial_snapshot)
    │  lake env lean tests/render/Cases.lean
    ▼
cases/<name>/props.json          -- via spytialPayloadProps, the same entry
    │                               point #spytial hands the infoview
    │  lake build renderHarnessJs
    ▼
dist/harness.js                  -- entry.mjs + widget/dist/spytialWidget.js
    │                               + react + the spytial-core bundles
    │  render.spec.mjs (Playwright, in ./Dockerfile's container)
    ▼
baseline/<name>.png (committed)  +  out/<name>/{page.html,render.svg,metrics.json}
```

The harness mounts the compiled component the infoview embeds, resolves
spytial-core through the same `widget/rollup.virtual.mjs`, and builds props from
the same `spytialPayloadProps` — so a pass is evidence about the real render.

## Running

```sh
just render              # full suite
just render -g rbtree    # one case (playwright title filter)
just render-update       # re-bless baselines — inspect the PNGs first!
just render-review       # kitty: re-blessed baselines vs HEAD, side by side
```

Needs `docker` (or `SPYTIAL_CONTAINER=podman`); `render-review` also needs a
kitty terminal. Failures write actual/expected/diff PNGs to `out/test-results/`
and a report to `out/report/index.html`.

## Why a container

A baseline is only meaningful if every pixel-affecting input is pinned, and the
host pins none of them:

- **Browser** — the image's bundled Chromium, digest-pinned.
- **Font** — spytial-core asks for Atkinson Hyperlegible and `@import`s it from
  Google Fonts. The image installs it locally and the suite runs with
  `--network none`, so the render can't vary with the network. This image's own
  `sans-serif` is a CJK face, so fallback is not an option.
- **Rasterization** — hinting, subpixel AA and Skia's CPU-dependent SIMD paths,
  pinned by launch flags in `playwright.config.mjs`.

So a baseline is comparable only to a render from this image; changing the image
means re-blessing all of them.

## Adding a case

Add a line to `Cases.lean`:

```lean
#spytial_snapshot "my-case" myValue with [.hideAtom (selector := "Nat")]
```

then `just render-update` and commit the new `baseline/my-case.png` — after
looking at it. `cases/` is generated and cleared by `just render`, so deleting a
case here really does retire its test.

## Settle protocol

`entry.mjs` is passive: it mounts the widget and records the graph element's
`layout-complete` / `constraint-error` / `layout-generation-error` events on a
document capture listener. The spec polls for those from the node side, because
headless Chromium throttles in-page timers while CDP evaluates always run, then
leans on `toHaveScreenshot`'s two-identical-frames stabilization for any
animation tail.

SVG byte-stability is *not* a settle signal — the solver pauses mid-layout long
enough to fake it, and baselines once captured a "Computing layout... 8%" toast.
That toast's visibility is now an explicit assertion.

`metrics.json` records node centers/sizes/fills, edge lengths and straightness
(`null` = never routed), and group boxes, for diagnosing drift without opening
the report.

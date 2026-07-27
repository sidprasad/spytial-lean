default:
    @just --list

build:
    lake build

# headless unit tests
test:
    lake build SpytialTests

# elaborate every demo
demos:
    lake build Demos

# image-snapshot render tests (Playwright + host Chrome; see tests/render/README.md)
render *args:
    lake build Demos renderHarnessJs
    lake env lean tests/render/Cases.lean
    rm -rf tests/render/out
    cd widget && pnpm exec playwright test --config ../tests/render/playwright.config.mjs {{args}}

# re-bless render baselines — inspect the PNGs before committing
render-update:
    @just render --update-snapshots

# rebuild widget JS and re-embed it
widget-reload:
    cd widget && pnpm run build
    lake build

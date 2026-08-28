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

# rebuild widget JS and re-embed it
widget-reload:
    cd widget && pnpm run build
    lake build

# rewrite the SGQ lowering golden after a deliberate change; read the diff.
# `lake env lean` re-elaborates the test unconditionally (`lake build` would
# consider it up to date) but runs against existing oleans, so build first.
rebless-sgq:
    lake build SpytialLean
    SPYTIAL_REBLESS=1 lake env lean tests/SelectorLoweringTest.lean

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

# the golden pins the exact SGQ text the lowering emits -- the wire contract
# nothing type-level checks. blessing is manual because a golden the build
# rewrites pins nothing: rewrite, then read the diff.
rebless-sgq:
    lake build SpytialLean
    SPYTIAL_REBLESS=1 lake env lean tests/SelectorLoweringTest.lean

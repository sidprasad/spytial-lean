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

# regenerate SpytialLean/SpecGenerated.lean from spytial-core's language manifest
gen-spec:
    lake exe specCodegen

# fail if the checked-in generated spec surface is stale
check-spec:
    lake exe specCodegen --check

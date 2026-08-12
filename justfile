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

# regenerate the SGQ lowering tables from simple-graph-query's manifest
gen-sgq:
    lake exe sgqCodegen

# fail if the checked-in tables no longer match the manifest
check-sgq:
    lake exe sgqCodegen --check

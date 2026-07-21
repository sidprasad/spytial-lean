default:
    @just --list

build:
    lake build

# relationalizer naming unit tests (TypeShape)
test:
    lake build SpytialTests

# elaborate every demo
demos:
    lake build Demos

# rebuild widget JS and force the include_str re-embed
widget-reload:
    cd widget && pnpm run build
    rm -f .lake/build/lib/lean/SpytialLean/Widget.*
    lake build

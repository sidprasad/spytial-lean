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

# rebuild widget JS and re-embed it
widget-reload:
    cd widget && pnpm run build
    lake build

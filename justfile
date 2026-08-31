default:
    @just --list

build:
    lake build

# headless unit tests
test:
    lake build SpytialTests
    pnpm -C widget test

# elaborate every demo
demos:
    lake build Demos

# rebuild widget JS and re-embed it
widget-reload:
    cd widget && pnpm run build
    lake build

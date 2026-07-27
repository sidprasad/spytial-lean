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

# side-by-side (old | new) review of re-blessed baselines, in-terminal via kitty icat
render-review:
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}"
    mapfile -t changed < <(git diff --name-only HEAD -- tests/render/baseline/)
    mapfile -t added < <(git ls-files --others --exclude-standard -- tests/render/baseline/)
    if [ ${#changed[@]} -eq 0 ] && [ ${#added[@]} -eq 0 ]; then
        echo "baselines match HEAD — nothing to review"; exit 0
    fi
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    for f in "${changed[@]}"; do
        echo "== ${f##*/} (old | new)"
        git show "HEAD:$f" > "$tmp/old.png"
        magick "$tmp/old.png" "$f" +append "$tmp/sxs.png"
        kitten icat --align left "$tmp/sxs.png"
    done
    for f in "${added[@]}"; do
        echo "== ${f##*/} (new, no previous)"
        kitten icat --align left "$f"
    done

# rebuild widget JS and re-embed it
widget-reload:
    cd widget && pnpm run build
    lake build

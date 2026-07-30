container := env_var_or_default('SPYTIAL_CONTAINER', 'docker')
render_image := 'spytial-render'

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

# build the render container (layer-cached; a no-op once warm)
render-image:
    {{container}} build -q -t {{render_image}} tests/render

# image-snapshot render tests (containerized; see tests/render/README.md)
render *args: render-image
    lake build Demos renderHarnessJs
    # stale case dirs would otherwise keep producing green tests forever
    rm -rf tests/render/cases tests/render/out
    lake env lean tests/render/Cases.lean
    # --network none is load-bearing: it stops spytial-core's Google Fonts
    # @import from making the render depend on the network. shm-size because
    # Chromium crashes on the default 64M /dev/shm.
    {{container}} run --rm --init --shm-size=1g --network none \
        --user "$(id -u):$(id -g)" -e HOME=/tmp \
        -v "$(pwd)":/repo -w /repo/tests/render \
        {{render_image}} node_modules/.bin/playwright test {{args}}

# re-bless render baselines — inspect the PNGs before committing
render-update:
    @just render --update-snapshots

# side-by-side (old | new) review of re-blessed baselines, in-terminal via kitty icat
render-review:
    #!/usr/bin/env bash
    set -euo pipefail
    # `montage -label` is the obvious tool here but has no default font on
    # NixOS, hence +append with the filename printed above each pair.
    for tool in magick kitten; do
        command -v "$tool" >/dev/null ||
            { echo "render-review needs $tool (kitty terminal + imagemagick)"; exit 1; }
    done
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

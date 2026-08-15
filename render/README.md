# Snapshot renders

`#spytial_snapshot "<name>" <term> (with <ops>)?` writes `cases/<name>/props.json`
beside its file (run it with `lake env lean <file>`); `render.mjs` renders each
case to a PNG in headless Chromium. The container pins Chromium (by digest),
the widget font, and rasterization flags, so renders compare across machines.

```sh
lake build renderHarnessJs
docker build -q -t spytial-render render
docker run --rm --init --shm-size=1g --network none \
  --user "$(id -u):$(id -g)" -e HOME=/tmp \
  -v "$(pwd)":/repo -w /repo \
  spytial-render node render/render.mjs /repo/<dir>/cases /repo/<dir>/out
```

From a downstream repo the harness sits in the dependency checkout, inside the
same mount: `H=.lake/packages/spytialLean`, build with
`(cd "$H" && pnpm install && lake build renderHarnessJs)`, and render with
`node "$H/render/render.mjs" ...` in the container run above.

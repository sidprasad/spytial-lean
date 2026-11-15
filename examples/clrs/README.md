# CLRS-Lean compatibility checks

This harness checks whether selected, unchanged CLRS-Lean sources compile with
the Lean/Mathlib version used by Spytial-Lean. It also checks concrete algorithm
results and Spytial inspection of the upstream red-black-tree datatype.

Working fork: <https://github.com/sidprasad/CLRS-Lean>

Original upstream: <https://github.com/TankTechnology/CLRS-Lean>

The local clone uses `origin` for the working fork and `upstream` for the
original repository. Its `main` branch tracks `origin/main`.

The investigated commit is `9352a92ba9b1d44ad1349f9e57ac31c858ec81b8`.
Its original toolchain is Lean `4.32.0-rc1`; Spytial-Lean uses `4.33.1`.

## Results (2026-11-13)

| Check | Lean/Mathlib 4.32.0-rc1 | Lean/Mathlib 4.33.1 |
| --- | --- | --- |
| Eight unchanged upstream modules | Passed | Passed |
| Concrete rotations and union-find operations | Passed | Passed |
| Four correctness theorems use only standard axioms | Passed | Passed |
| Concrete and proof-context Spytial inspection | Not targeted | Passed |

Spytial-Lean's own build also passed. No upstream definitions or proofs needed
changes. Exact dependency revisions, source hashes, and check results are saved
in [compatibility-results.json](compatibility-results.json). These results support
using the selected CLRS modules with Spytial-Lean's current toolchain; they do not
establish whole-repository or website compatibility.

## Annotating imported data structures

[RedBlackTree.lean](RedBlackTree.lean) attaches a `spytial_spec` directly to
`CLRS.Chapter13.RBTree`. This plays the same role as the Python `@orientation`,
`@attribute`, and `@atomStyle` decorators in `spytial-clrs/src/trees.ipynb`.
The specification is registered separately from the imported datatype and becomes
its default layout. No wrapper datatype or upstream source edit is required.

The example positions left/right subtrees, aligns siblings, displays keys as
attributes, hides empty leaves, and selects red/black styles using the original
`RBTree.rootColor` function. Empty endpoints are excluded from the orientation
constraints, just as the Python example excludes its shared NIL sentinel.

CLRS-Lean's constructor arguments are positional, so the captured field names are
`node_0` (color), `node_1` (left), `node_2` (key), and `node_3` (right).

The snapshot is written to
`examples/clrs/cases/annotated-red-black-tree/props.json`. Its verified preview is
`output/clrs-annotations/annotated-red-black-tree.png`: seven displayed nodes,
six edges, and no layout conflicts. This preview uses the installed Chromium
for a visual smoke check.

## Scope

The source checks compile eight modules: red-black trees, three pointer-rotation
modules, abstract disjoint-set operations, executable disjoint-set forests,
graph representation, and BFS. Each module is compiled directly from the clone,
with its original imports and with Verso docstring checking enabled. Source
hashes, dependency revisions, compiler output, and timings are recorded.

`Smoke.lean` checks concrete rotations and union-find operations, and prints the
axiom dependencies of selected upstream correctness theorems. `SpytialSmoke.lean`
exercises both `#spytial` on a concrete upstream tree and tactic-mode `spytial`
with abstract subtrees and black-height hypotheses.

This is a focused library compatibility check. It does not build the entire
CLRS library, its documentation website, or its Verso dependencies. Each Lean
version needs its matching Mathlib and transitive dependencies; compiled Lean
artifacts must not be reused across compiler versions.

## Run against the existing Spytial/Mathlib environment

Run from the Spytial-Lean repository root. The `examples/mathlib` environment
must already have its dependencies and Mathlib cache installed.

```sh
git clone https://github.com/sidprasad/CLRS-Lean.git tmp/clrs-compat/CLRS-Lean
git -C tmp/clrs-compat/CLRS-Lean remote add upstream https://github.com/TankTechnology/CLRS-Lean.git
git -C tmp/clrs-compat/CLRS-Lean checkout 9352a92ba9b1d44ad1349f9e57ac31c858ec81b8

python3 examples/clrs/check_compat.py \
  --checkout tmp/clrs-compat/CLRS-Lean \
  --environment examples/mathlib \
  --output tmp/clrs-compat/results/4.33.1 \
  --check-file examples/clrs/Smoke.lean \
  --check-file examples/clrs/SpytialSmoke.lean \
  --check-file examples/clrs/RedBlackTree.lean
```

The runner obtains the compiler and import paths through the chosen Lake
environment. It writes the CLRS build artifacts into the output directory,
without changing the upstream source or the Spytial-Lean toolchain.

To rerun only the small checks after a completed source build, pass
`--checks-only` with the same arguments. The runner verifies the compiler version
and upstream commit against the recorded source build.

For a baseline comparison, supply a Lake environment pinned to Lean and Mathlib
`4.32.0-rc1`, use a separate output directory, and omit `SpytialSmoke.lean`.
Spytial-Lean itself remains on `4.33.1`.

The baseline environment's configuration is retained in
`tmp/clrs-compat/environments/4.32.0-rc1`. Its downloaded dependencies were removed
after verification to recover disk space; run `lake exe cache get` there before
repeating the baseline checks.

Raw logs and per-module results live in `tmp/clrs-compat/results/`. These caches
and the upstream clone are excluded from the parent repository's tracked files.

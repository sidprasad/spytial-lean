# Spytial for Lean

Spytial draws Lean values in the VS Code infoview. Inside a function or proof,
it uses local hypotheses to draw the known parts of a value and leaves the rest symbolic.

## Install

Use the [project’s Lean version](lean-toolchain), Node.js 24, and pnpm 11.
Add the dependency to your `lakefile.lean`:

```lean
require spytialLean from git "https://github.com/sidprasad/spytial-lean" @ "main"
```

Run `lake update spytialLean`, then `lake build SpytialLean`.
For the tagged release, follow the [v0.2.1 installation instructions](https://github.com/sidprasad/spytial-lean/blob/v0.2.1/README.md).

## Inspect a value

```lean
import SpytialLean

#spytial ([7, 8] : List Nat)

theorem headOfKnownCons (xs tail : List Nat) (h : xs = 7 :: tail) :
    xs.head? = some 7 := by
  spytial xs
  simp [h]
```

With the Lean 4 extension, place the cursor on either inspection. The first draws
the list `[7, 8]`. The second uses `h` to draw `xs` with head `7` and tail `tail`.
Inside a function, wrap an expression as `spytial e` to inspect its value.

[Layouts](docs/layout.md) · [Observations](docs/observations.md) · [Proof contexts](docs/context-inspection.md) · [Comparing inspections](docs/theorem-inspections.md) · [Development guide](DEVGUIDE.md)

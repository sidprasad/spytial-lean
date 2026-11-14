# Spytial for Lean

Draw Lean values in the VS Code infoview. Inside a proof, `spytial` uses
local hypotheses to show what is known about a value.

## Install

Use the Lean version in [`lean-toolchain`](lean-toolchain). Install Node.js 24
and pnpm 11 to build the widget. Add this dependency to your `lakefile.lean`.

```lean
require spytialLean from git "https://github.com/sidprasad/spytial-lean" @ "v0.2.0"
```

Run `lake update spytialLean`, then `lake build SpytialLean`.

## Try it

```lean
import SpytialLean

#spytial ([7, 8] : List Nat)

example (xs tail : List Nat) (h : xs = 7 :: tail) : xs.head? = some 7 := by
  spytial xs
  simp [h]
```

In VS Code with the Lean 4 extension, place the cursor on either `spytial`
line. The first draws a complete list. In the proof, the diagram shows that
`xs` has head `7` and tail `tail`, even though the tail's elements are unknown.

See [layout specifications](docs/layout.md) to customize a diagram or
[proof contexts](docs/context-inspection.md) to see which facts it includes.
Place the cursor on a theorem's name to [compare its proof inspections](docs/theorem-inspections.md).

[Development guide](DEVGUIDE.md)

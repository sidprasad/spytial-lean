# Spytial for Lean

Draw complete and partially known Lean values in the VS Code infoview. Inspect
an expression inside a function or proof, using local hypotheses to show its
known structure and relations.

## Install

The examples below use the development version. Use the Lean version in
[`lean-toolchain`](lean-toolchain), Node.js 24, and pnpm 11. Add this dependency
to your `lakefile.lean`:

```lean
require spytialLean from git "https://github.com/sidprasad/spytial-lean" @ "main"
```

Run `lake update spytialLean`, then `lake build SpytialLean`.

For the tagged `v0.2.1` release, pin `@ "v0.2.1"` and follow its
[release README](https://github.com/sidprasad/spytial-lean/blob/v0.2.1/README.md).
Function-expression inspections and newer evidence controls require the
development version.

## Try it

```lean
import SpytialLean

#spytial ([7, 8] : List Nat)

theorem headOfKnownCons (xs tail : List Nat) (h : xs = 7 :: tail) :
    xs.head? = some 7 := by
  spytial xs
  simp [h]
```

In VS Code with the Lean 4 extension, place the cursor on either `spytial`
line. The first draws a complete list. In the proof, the diagram shows that
`xs` has head `7` and tail `tail`, even though the tail's elements are unknown.

See [layout specifications](docs/layout.md) to customize a diagram or
[proof contexts](docs/context-inspection.md) to see which facts it includes.
Place the cursor on `headOfKnownCons` and expand **Spytial inspections** in the
infoview to [open its recorded inspection](docs/theorem-inspections.md).

## Inside a function

Wrap an expression with `spytial` to inspect it while Lean checks the function.
The expression supplies the value of the surrounding computation.

```lean
def swapFirstTwo : List Nat → List Nat
  | a :: b :: tail =>
    let lower : List Nat := spytial (.cons a tail) titled "New tail"
    spytial (.cons b lower) titled "Result"
  | xs => xs
```

Place the cursor on either `spytial` line for its diagram, or on `swapFirstTwo`
and expand **Spytial inspections** to compare the new tail with the result.
Both views keep the rest of the list symbolic.

## Context and evidence

Function and proof inspections use bounded Aesop normalization with Lean
simplification and selected forward rules. Evidence consists of ordinary Lean
proof terms checked in their original scope. Whole-value commands use structural
computation. See [evidence and context preparation](docs/evidence.md) for the
contract and adapter responsibilities.

[Development guide](DEVGUIDE.md)

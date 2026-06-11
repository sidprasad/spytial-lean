import SpytialLean

open SpytialLean

/-! # Enumeration

`#spytial.enumerate <Type>` enumerates ALL inhabitants of a finite type and
renders the entire population in a single spatial diagram.

A type is enumerable when `tryEnumerateDomain` can list its elements:

* `Bool` — `false`, `true`,
* `Fin n` for `n ≤ 20` — `0 … n-1`,
* an inductive type whose constructors *all* take no arguments (a plain enum).

There is deliberately **no `Fintype` support**: that lives in Mathlib, and the
core library and default demos stay Mathlib-free. Non-enumerable types get a
clear error naming what is supported (see the failing case at the bottom).

Every inhabitant is walked into ONE shared diagram, so structurally identical
subterms across the population unify (the relationalizer's `seen` cache is
shared across the whole enumeration).
-/

/-! ## A custom enum -/

/-- A three-element enumeration. All constructors take no arguments, so the type
    is enumerable. -/
inductive Three where
  | a | b | c
  deriving Repr

-- Renders three atoms labeled `a`, `b`, `c` in a single diagram.
#spytial.enumerate Three

-- Inspect the JSON: exactly three atoms, no relations.
#spytial.enumerate.datum Three

/-! ## Built-in finite types -/

-- `Bool` enumerates to `false`, `true`.
#spytial.enumerate Bool

-- `Fin 5` enumerates to `0, 1, 2, 3, 4`.
#spytial.enumerate (Fin 5)

#spytial.enumerate.datum Bool
#spytial.enumerate.datum (Fin 5)

/-! ## Enumerating a mapping — `#spytial f` already does this

The issue's motivating example is a function on a finite domain. A natural ask
is a `#spytial.map f` command that draws the function's graph. It is
*unnecessary*: `#spytial f` ALREADY enumerates the mapping. When the
relationalizer reaches a `λ` whose domain is enumerable, it takes the
extensional view — it enumerates every input and emits one input→output edge.
So plain `#spytial f` on a `Three → Three` shows the graph `a→b`, `b→c`, `c→a`
directly, and a separate `#spytial.map` variant would be redundant. -/

/-- The issue's motivating map: a cyclic permutation of `Three`. -/
def f : Three → Three
  | .a => .b
  | .b => .c
  | .c => .a

-- No `#spytial.map` needed: the lambda's finite domain is enumerated here,
-- producing the mapping graph a→b, b→c, c→a.
#spytial f
#spytial.datum f

/-! ## Spec lookup

A spec attached to the enumerated type (via `spytial_spec`) is used as the
default, just like `#spytial` looks up the spec of a value's type. An explicit
`with [...]` overrides it. -/

spytial_spec Three [
  .atomColor (selector := "Three") (value := "#4CAF50")
]

-- Uses the spec attached to `Three`.
#spytial.enumerate Three

-- Explicit `with [...]` overrides the attached spec.
#spytial.enumerate Three with [
  .atomColor (selector := "Three") (value := "#2196F3")
]

/-! ## Failing case — non-enumerable type

`Nat` has infinitely many inhabitants, so it is not enumerable. Uncommenting the
line below produces:

  #spytial.enumerate cannot enumerate 'Nat'. Enumerable types are: Bool,
  Fin n (n ≤ 20), and inductive types whose constructors all take no arguments.
-/

-- #spytial.enumerate Nat -- error: not enumerable

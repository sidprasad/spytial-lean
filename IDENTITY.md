# Atom identity in the Lean relationalizer

*How this integration decides when two pieces of a value are drawn as one
node — and why that is a declaration, not a walker heuristic.*

## The problem

A Spytial diagram is a relational structure extracted from a value: atoms and
edges. Extraction has to answer a question the formal model takes as given:
**when do two occurrences of "the same" data become one atom?** Every
integration answers it somehow. Python uses heap identity (`id()`), so sharing
is whatever allocation produced — which is why the BDD corpus builds singleton
terminals and a unique table before it can draw one shared `tt`. Rust's
exporter merges nullary variants and nothing else. And this integration's
previous walker merged subterms whose *spellings* hashed equal, which is wrong
in both directions at once:

```lean
inductive Tree | leaf (n : Nat) | node (l r : Tree)

def A := node (leaf 1) (leaf 1)
def B := node (leaf 1) (leaf (0+1))   -- the same value, spelled differently
```

`A` drew three atoms (the equal leaves silently merged); `B` drew four (the
parents split while their children merged). Same value, two pictures, one of
them internally inconsistent. Worse, the merging in `A` was never asked for —
and a shared leaf atom cannot be simultaneously `left` and `right` of its
parent, so orientation specs on equal siblings became unsatisfiable with no
Lean-side signal. That failure was reported from real use.

The root cause is not a bug in the memo; it is a category error. Whether two
occurrences are "the same" is a fact about the **domain** being drawn — a BDD,
a set, a syntax tree — not about the walker. Different domains genuinely
answer differently: two equal sub-BDDs *are* one node; two occurrences of
`Var "x"` in a syntax tree are *different* program points. So identity must be
**declared per type**, and in Lean, per-type declared structure is a
typeclass.

## The design in one sentence

**Every value gets an identity; subterms with the same identity merge into one
atom; no declaration means no merging — the term draws as written, literals
included.**

Identity is computed as a *key*, not by pairwise comparison: two subterms
merge exactly when their keys are equal. Equal-keys is transitive whatever
anyone writes, so the grouping is always coherent and independent of walk
order, and each subterm costs one key computation instead of comparisons
against everything seen.

## Declaring identity

```lean
class SpytialIdentity (α : Type u) where
  via   : IdentityVia α             -- how values of α are identified
  norm? : Option (α → α) := none    -- display: canonical representative

inductive IdentityVia (α : Type u)
  | identity (f : α → IdentityKey)  -- a classifier: merge iff equal keys
  | eqv (r : α → α → Bool)          -- reuse your equality (see below)
```

- **No instance** — the term as written. The default, because merging without
  a declaration asserts a sameness nobody stated.
- **`deriving SpytialIdentity`** — structural identity for any inductive:
  equal values are one atom, computed on values (`leaf (0+1)` merges with
  `leaf 1`). This is the flagship: *naive data gets sharing for free*. The
  demo (`demos/BDD.lean`) Shannon-expands a boolean function with no unique
  table, no manager, no hash-consing — 22 atoms as written, 12 under the
  derived instance (one `tt`, one `ff`, equal subtrees merged), 6 after the
  reduction pass. The renderer's identity table plays the unique table so the
  program never has to.
- **A custom classifier** — for domains whose sameness is a genuine quotient
  of the representation: key on the fields that matter
  (`.identity fun t => toKey t.payload` — provenance dropped), key on a
  normal form (`.identity fun c => toKey c.s.toLower`). Any function is
  allowed; the design does not second-guess declarations.
- **`.eqv`** — reuse an equality relation directly, e.g.
  `SpytialIdentity.ofBEq` for `.eqv (· == ·)`. First-class, because some
  equivalences are genuinely relational with no reasonable classifier (a
  multiset over elements with equality but no ordering or hash). The relation
  must be an actual equivalence — reflexive, symmetric, transitive —
  deliberately *not* `LawfulBEq`: relations coarser than `=` are exactly the
  point. With a genuine equivalence the resulting partition is independent of
  walk order; the costs are one compiled comparison per existing group (vs. a
  table lookup) and no key-derived stable naming.

### Encoding is not identity

Deriving over a `Nat` field must write the field's value into the parent's
key — but that must not make every `Nat` atom in every diagram merge. Two
different judgments, two classes:

```lean
class ToIdentityKey (α : Type u) where
  toKey : α → IdentityKey           -- "values can be written into a key"
```

Primitives (`Nat`, `String`, `Bool`, `Int`, `Char`, the `UInt`s) have global
`ToIdentityKey` instances — harmless, since encoding grants no merge
behavior — plus lifts through `List`/`Array`/`Option`/`Prod`. No primitive
has a `SpytialIdentity` instance. Consequence: a type with a `List Nat` field
derives (the encoding lifts), while `List Nat` *atoms* never merge
undeclared. Derived fields route through the field type's `SpytialIdentity`
when one is declared, else its encoding.

## Views: one value, several granularities

The point of a render is a useful observation, and one document often wants
the *same value* at more than one granularity — the BDD demo's whole story is

```lean
#spytial (Raw.mk fTree)   -- as written: the naive expansion
#spytial fTree            -- declared sharing: the lens changed, not the value
#spytial fTree.reduce     -- the ROBDD: the value changed, not the lens
```

`Raw α` is `α` under a different name (the same device as Mathlib's
`OrderDual`): the walk draws its whole subtree as written, and the wrapper
itself never appears in the picture. `Viewed α` is the dual — inside a `Raw`
region it returns to declared identity — quasiquote and unquote, for
diagrams. Formally, the walk carries an ambient mode (`declared` /
`asWritten`); wrappers shift it for a subtree. Identity stays per-type and
declared; only the *viewing* is contextual. This fits how Lean already works:
the language has several notions of sameness (`=`, `==`, `≈`, definitional
equality) and a standing idiom for "same carrier, different structure" —
wrapper types with their own instances.

Two further rules keep pictures honest:

- **Holes are not policy.** Occurrences of one metavariable are one atom
  under every mode — filling it fills every position. Open subterms have no
  value, hence no identity: they draw as written.
- **Deliberate opacity is respected.** A leaf whose head is `@[irreducible]`
  or `opaque` identifies by its *spelling* — two occurrences merge with each
  other and with nothing else. Default disciplines do not evaluate through a
  barrier the author declared; an explicit instance may, because barriers
  hold against defaults, not against declarations.

## What the implementation guarantees

The specification is one sentence: *give every subterm a fresh atom, then
merge occurrences with the same `(type, identity)`.* The fresh-atom half is
exactly the model in `Fidelity.lean`; declared identity is a coarsening of it
by quotient, decided per type. The shipped walker fuses the two passes, and a
literal two-pass reference implementation lives alongside it: the test suite
runs both over a battery of fixtures — sharing, spelling variants, `.eqv`
domains, view wrappers, holes, opacity, custom relationalizers — and requires
identical output. The walker's structural keys are additionally cross-checked
byte-for-byte against the compiled derived classifiers, so the meta-level
computation and the runtime declaration cannot drift apart. Merging is
intra-type by construction (the atom table is keyed on the full elaborated
type), custom `spytial_relationalizer`s take precedence over any identity
instance, and no data structure anywhere keys on a bare hash.

## Current limitations

- **Representative display (`norm?`)**: merging honors the declaration, but
  the drawn representative is currently the first occurrence encountered, not
  the normal form — drawing `norm x` requires reifying an evaluated value
  back into an expression, which is not generally available. Deferred rather
  than shipped half-working; merging is unaffected either way.
- **Roles as type synonyms**: a one-field structure works today as a role
  (`structure VarIdx where i : Nat deriving SpytialIdentity`); a bare
  `def VarIdx := Nat` does not yet, because the walker normalizes types
  before consulting instances. Planned.
- **`deriving` limits**: nested and indexed inductives, function-typed
  fields, and fields depending on earlier fields are rejected with ordinary
  errors. A parametric user type applied to a primitive needs a hand-written
  `ToIdentityKey` lift until `deriving ToIdentityKey` exists.
- **`.eqv` costs** scale with the number of groups per type, and an
  ill-behaved relation (e.g. `Float`'s `==`, which is not reflexive at `NaN`)
  makes the grouping walk-order-dependent — the relation's equivalence laws
  are the declaration's obligation.

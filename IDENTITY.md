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
a set, a syntax tree — not about the walker, and never a fact about what
allocation produced or how the term was spelled. Different domains genuinely
answer differently: two equal sub-BDDs *are* one node; two occurrences of
`Var "x"` in a syntax tree are *different* program points. So identity must be
**declared per type**, and in Lean, per-type declared structure is a
typeclass.

## The design in one sentence

**Every value gets an identity; subterms with the same identity merge into one
atom; no declaration means no value-based merging — the term draws as written,
literals included.** The one undeclared merge is not value-based: a
*reference* — a metavariable, a hypothesis — is drawn once however often it
occurs (the references rule below).

In the primary presentation, identity is computed as a *key*, not by pairwise
comparison: two subterms
merge exactly when their keys are equal. Equal-keys is transitive whatever
anyone writes, so the grouping is always coherent and independent of walk
order, and each subterm costs one key computation instead of comparisons
against everything seen.

## Declaring identity

```lean
class SpytialIdentity (α : Type u) where
  via   : IdentityVia α             -- how values of α are identified
  norm? : Option (α → α) := none    -- display representative; law:
                                    --   identity (norm x) = identity x

inductive IdentityVia (α : Type u)
  | identity (f : α → IdentityKey)  -- a classifier: merge iff equal keys
  | eqv (r : α → α → Bool)          -- reuse your equality (see below)
```

- **No instance** — the term as written. The default, because merging without
  a declaration asserts a sameness nobody stated.
- **`deriving SpytialIdentity`** — the structural identity, for any inductive.
  Precisely: the structural congruence induced by the fields — each field
  routes through its own type's declared identity when one exists, else
  through its exact value encoding — computed on values, so `leaf (0+1)`
  merges with `leaf 1`. "Equal values are one atom" is the whole story
  exactly when no field declares something coarser. This is the flagship:
  naive data opts into sharing with one deriving clause. The demo
  (`demos/BDD.lean`) Shannon-expands a boolean function with no unique table,
  no manager, no hash-consing — 22 atoms as written, 12 under the derived
  instance (one `tt`, one `ff`, equal subtrees merged), 6 after the reduction
  pass. For purposes of the rendered graph, the identity table plays the
  unique table so the program never has to build one.
- **A custom classifier** — for domains whose sameness is a genuine quotient
  of the representation: key on the fields that matter
  (`.identity fun t => toKey t.payload` — provenance dropped), key on a
  normal form (`.identity fun c => toKey c.s.toLower`). Any function is
  allowed; the design does not second-guess declarations. A classifier
  coarser than structural makes the drawn atom a class *representative* —
  see "What a quotient picture shows" below.
- **`.eqv`** — reuse an equality relation directly, e.g.
  `SpytialIdentity.ofBEq` for `.eqv (· == ·)`. First-class, because some
  equivalences are genuinely relational with no reasonable classifier: a
  multiset over elements whose own identity is itself relational — the
  elements merge by their declared relation, so there are no element keys to
  sort into a canonical container form. It is also what derived instances
  degrade to when a field is decider-presented (the field rule below), which
  keeps composition total. The relation must be an actual equivalence —
  reflexive, symmetric, transitive — deliberately *not* `LawfulBEq`:
  relations coarser than `=` are exactly the point. With a genuine
  equivalence the resulting partition is independent of walk order; the costs
  are up to one compiled comparison per existing group — linear in the number
  of groups, worst case — and no key-derived stable naming.

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
when one is declared, else its encoding. Presentations propagate through that
rule: a derived instance stays classifier-presented only while every
identity-routed field has a classifier; one decider-presented field degrades
the composite to a decider, since a key cannot be built from comparisons. The
partition is the declared one either way — what degrades is cost (group
comparisons instead of key lookups) and key-derived naming.

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
`asWritten`); wrappers shift it for a subtree, nesting lexically — the
innermost wrapper wins (`Raw (Viewed τ)` walks declared, `Viewed (Raw τ)` as
written). Wrappers never reach the atom table: an as-written region allocates
fresh atoms without consulting it, and a `Viewed` payload keys at its own
unwrapped type, rejoining the partition outside its `Raw` region. (The walker
recognizes wrappers on the type before normalization — why the semireducible
wrappers survive where `def` synonyms melt.) Identity stays per-type and
declared; only the *viewing* is contextual. This fits how Lean already works:
the language has several notions of sameness (`=`, `==`, `≈`, definitional
equality) and a standing idiom for "same carrier, different structure" —
wrapper types with their own instances. The same idiom covers a carrier
needing two *positive* notions of identity (syntax up to source locations and
syntax up to alpha, say): the second notion is a wrapper type carrying its
own declaration. `Raw` itself only ever selects between a type's declared
identity and none.

Two further rules keep pictures honest:

- **References are drawn once.** A leaf reference — a metavariable, or a
  hypothesis (free variable) — is one atom per reference under every mode:
  `?m` twice is one hole (filling it fills every position), `x` twice is one
  hypothesis. This is referential identity, not value-based merging: the term
  contains one thing in two positions, so the drawn structure is genuinely a
  DAG there, and a spec that assumes tree shape (say, left/right orientation
  over repeated occurrences of one reference) is unsatisfiable because the
  term is not a tree. A *compound* open subterm has no value, hence no value
  identity: its spine draws as written, occurrence-distinct, while closed
  subtrees beneath it keep their declared identity and references within it
  stay interned.
- **Deliberate opacity is respected.** Default disciplines do not evaluate
  through a barrier the author declared: while computing a *declared*
  identity, the walk stops at an `@[irreducible]` or `opaque` head and keys
  the stuck subterm by its exact term structure instead. Structurally
  identical closed terms are the same term, hence certainly the same value,
  so this merges only what the declared identity already licenses — a sound
  under-approximation, whose cost runs the other way: `f 3` and `f (2+1)`
  stay distinct atoms, since identifying them would mean unfolding `f`. Under
  a type with no declared identity the gate never fires — stuck leaves draw
  as written, one atom per occurrence — so opacity introduces no undeclared
  merging anywhere. An explicit `.identity`/`.eqv` instance runs compiled
  code, which cannot see reducibility attributes: a declaration computes
  through barriers by necessity. Barriers hold against defaults, not against
  declarations.

## What the implementation guarantees

The specification is still short: *give every occurrence a fresh atom, then
quotient — closed subterms by their type's declared identity, references
(metavariables, hypotheses) by referential identity, opaque-stuck subterms
within declared types by term structure; everything else stays
occurrence-distinct.* The fresh-atom half is exactly the model in
`Fidelity.lean`; declared identity is a coarsening of it by quotient, decided
per type. The closedness clause means whether a declared identity applies at
an occurrence depends on the term, not only the type: a closed `leaf 1` under
an open spine still merges, while the spine itself stays occurrence-distinct.

**What a quotient picture shows.** A merged atom is drawn from one member of
its identity class — the first occurrence the walk reaches — with that
member's label and fields; a repeated identity returns the existing atom
without walking the new occurrence's subtree. Under structural identity the
choice is invisible, because all members of a class are structurally
identical. Under a coarser identity it is the semantics: fields the key
ignores show one class member's values, and the picture determines the value
only up to the declared identity — which is exactly the sameness the
declaration asserts. Which member represents the class is walk order until
`norm?` display lands; `norm?` is how the representative becomes part of the
declaration rather than an accident of traversal.

The shipped walker fuses the two passes, and a literal two-pass reference
implementation lives alongside it: the test suite runs both over a battery of
fixtures — sharing, spelling variants, `.eqv` domains, view wrappers, holes,
opacity, custom relationalizers — and requires identical output. Where the
walk computes structural keys meta-level, they are cross-checked byte-for-byte
against the compiled derived classifiers, so the meta computation and the
runtime declaration cannot drift apart. Merging is intra-type by construction
(the atom table is keyed on the full elaborated type), custom
`spytial_relationalizer`s take precedence over any identity instance, and no
data structure anywhere keys on a bare hash.

## Current limitations

- **Representative display (`norm?`)**: the walker does not yet draw `norm x`
  for a merged group — reifying an evaluated value back into an expression is
  not generally available — so the representative is the first occurrence, as
  the guarantees section states. By the law `identity (norm x) = identity x`,
  merging is unaffected either way; deferred rather than shipped half-working.
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

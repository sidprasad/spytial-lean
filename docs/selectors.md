# The selector language

Selectors are simple-graph-query's relational expression/formula language,
embedded as Lean syntax (category `spytial_sel`, declared in
`SpytialLean/SelectorElab.lean`). This file is the language reference; the op
positions that accept selectors are listed in the README. "The engine" below is
simple-graph-query: spytial-core depends on it and evaluates selectors with it
at render.

The grammar below is not written by hand. Every rule is built from the
construct's production in simple-graph-query's `docs/sgq-language.json`, which
is generated from its ANTLR grammar; `SpytialLean/Sgq.lean` reads that manifest
into Lean tables as it elaborates. A construct added upstream gets a rule, a
kind check, an arity check and a lowering by rebuilding, with no edit to this
package. What is written by hand is listed at the end of this section.

## Grammar

Tiers bind tighter downward. The numbers are the engine's own precedence
levels, used verbatim: the parser holds no scale of its own, so a cascade that
moves upstream moves here. Binary operators are left-associative except
`implies`. There is one category, as there is one grammar upstream: a formula
and a relational expression sit in the same cascade, and which positions accept
which is a question about kinds, settled by the elaborator ("Typing" below)
rather than by the parser.

```ebnf
sel ::=
    "let" letBinds "|" sel                       (*  0: desugars by substitution *)
  | quantifier ["disj"] binders "|" sel          (*  0 *)
  | "sum" ["disj"] binders "|" sel               (*  0: aggregation; integer *)
  | sel ("||" | "or") sel                        (*  1 *)
  | sel "xor" sel                                (*  2 *)
  | sel ("<=>" | "iff") sel                      (*  3 *)
  | sel ("=>" | "implies") sel ["else" sel]      (*  4: right-associative *)
  | sel ("&&" | "and") sel                       (*  5 *)
  | ("!" | "not") sel                            (*  6 *)
  | sel [neg] cmp sel                            (*  7 *)
  | multiplicity sel                             (*  8: multiplicity test *)
  | sel "+" sel | sel "-" sel                    (*  9: union, difference *)
  | "#" sel                                      (* 10: cardinality; integer *)
  | sel "++" sel                                 (* 11: override *)
  | sel "&" sel                                  (* 12: intersection *)
  | sel [mult] "->" [mult] sel                   (* 13: product *)
  | sel "<:" sel | sel ":>" sel                  (* 14: domain / range restriction *)
  | sel "[" sel ("," sel)* "]"                   (* 15: box join / builtin call *)
  | sel "." sel                                  (* 16: join *)
  | "^" sel | "*" sel | "~" sel                  (* 17: closures, transpose *)
  | "@:" sel | "@str:" sel | "@bool:" sel        (* 17: label projections; value *)
  | "@num:" sel                                  (* 17: numeric projection; integer *)
  | ident                                        (* 18: relation, sig, binder, or ctor label *)
  | "univ" | "iden" | "none"
  | "{" binders "|" sel "}"                      (* 18: comprehension; arity = #binders *)
  | "{" sel* "}"                                 (* 18: block, a conjunction *)
  | "(" sel ")"
  | string                                       (* string literal *)
  | int                                          (* integer literal *)
  | "`" name                                     (* atom literal, a Lean name literal *)
  | "lean" "(" term ")"                          (* a Lean function; arity from its type *)

mult         ::= "lone" | "one" | "some" | "two" | "set"
multiplicity ::= "no" | "some" | "lone" | "one" | "two" | "set"
quantifier   ::= "all" | "no" | "some" | "lone" | "one" | "two"
letBinds ::= ident "=" sel ("," ident "=" sel)*
binders  ::= group ("," group)*
group    ::= ident ("," ident)* ":" sel
neg ::= "!" | "not"
cmp ::= "=" | "in" | "ni" | "is"
      | "<" | ">" | "<=" | ">=" | "=<"           (* integer comparisons; "=<" ≡ "<=" *)
```

The precedence is Forge's: implication binds tighter than `or` and `iff`
(`a || b => c` is `a || (b => c)`), and implication is the only
right-associative connective. Longest-match separates the quantifier
`some x : A | φ` from the multiplicity `some e`, whose operand extends down
through union (`some A + B` is `some (A + B)`). A box join binds looser than a
join, so `a.b[c]` is `(a.b)[c]` and `a[b].c` is a parse error in both languages
— write `(a[b]).c`. Whitespace matters twice: no space before a box-join `[`,
and none between `-` and an integer literal. A string is a literal value, so it
sits in a comparison operand and nowhere a selector is expected.

A negation is a slot of the comparison rather than an operator of its own, as
it is upstream, so `!=`, `not =`, `!in`, `not in`, `!ni` and `not ni` are one
rule with that slot filled. Negating an integer comparison parses and is then
rejected: there is no lowering for it, and the opposite operator says the same
thing. `a is b` parses and is rejected too — the manifest records that the
engine refuses to evaluate it.

A selector lexes under its own token table, which holds the engine's symbols
and nothing else. Two things follow. Lean's keywords are ordinary names here,
so a field called `fun` or `where` needs no escape. And the DSL's own symbols —
`@:`, `<:`, `<=>` and the rest — never reach the global token table, so
importing this package does not reserve them anywhere else.

An identifier is a single component. The selector lexer stops at a `.`, so the
dot is always the join operator and `a.b` and `a . b` are the same selector,
read as SGQ reads them — spacing carries no meaning, and a unary operator binds
tighter (`^a.b` is `(^a).b`). A name that must contain a dot is escaped with
guillemets: `«Untyped.Term»` for a qualified Lean type. So is a name that
collides with one of the grammar's own words: `«univ»` for a field named after
a nullary constant.

Relative to Forge, the label projections (`@:`, `@str:`, `@bool:`, `@num:`) are
SGQ/Spytial extensions, and atom literals are spelled as Lean name literals
(`` `a0 ``). The fragment omits Forge's declaration and temporal layers. Arrow
multiplicities (`A one -> lone B`) parse for grammar parity, but the engine
rejects them at render: they are declaration and constraint syntax, not part of
an expression.

**What is written by hand.** Five rules, none of which grows with the language:
the four literal forms (identifier, string, integer, atom literal), which are
lexical rather than constructs and which Lean's own lexer reads structurally;
and `let`, which the engine parses and refuses to run and which this package
implements by substitution. The named constants `univ`, `iden` and `none` have
no rule at all: their spellings are identifiers, so an atom-keyed rule would
never fire on an unspaced `univ.lo`, and they are read off the identifier
instead. `tests/SgqCoverageTest.lean` keeps that account and fails when a
construct upstream falls outside it.

## Meaning

| Form | Meaning |
|------|---------|
| `left`, `app_0` | a field relation (arity 2: parent → child) |
| `RBNode`, `String` | a type sig (arity 1: all atoms of that type) |
| `a[b, …]` | box join (`a[b] ≡ b.a`), kept as written |
| `{x, y : T \| φ}` | set comprehension (arity = number of binders) |
| `@:e`, `@str:e`, `@bool:e` | label projections (string/bool value reads) |
| `univ`, `iden` | the universe and identity relations |
| `lean (f)` | the tuples the Lean function `f` selects (arity from `f`'s type) |

**`let x = e, … | φ`** desugars by substitution at elaboration; the engine
never sees a `let`. A later binder shadows the `let`. A substitution that an
inner binder would capture is a compile error.

## Typing

The elaborator gives every expression one of the manifest's kinds — relation,
number, boolean, string — and every slot accepts the kind the manifest says it
accepts, so SGQ's silent scalar/tuple confusion (`some #e`) is a compile error.
A comparison accepts either kind on both sides and requires the two to agree,
so `#a = b` is an error rather than a coercion.

**Integer layer.** The integer forms are: `#e` (cardinality), integer
literals, `@num:e` (numeric projection), the builtins `add subtract multiply
divide remainder abs sign floor ceil`, the aggregators `sum[e]`, `min[e]`, and `max[e]`
(lowered through `@num:` — the engine aggregates numeric labels, not atom
ids), the `sum x : A | ie` aggregation quantifier, and the int comparisons.
Integer positions accept exactly these forms; tuple positions reject them.
Counting selectors like `#{x : T | φ} = 2` and `@num:(x.key) < 5` work.

**Label comparisons** accept nullary constructors (`@:x = nil`), string
literals, another projection (`@:vr = @:(y.v)`), or, opposite a `@bool:`
projection, the boolean literals `true`/`false`. Numeric labels go through
`@num:`. A comparison is exact equality against the label the relationalizer
gave the atom, and each literal form lowers to the spelling that makes that
equality hold for the value written: `@:x = nil` matches the atoms built by
the `nil` constructor, and `@str:(x.v) = "abc"` the `String` atom holding
`abc`. (A string literal carrying a character SGQ cannot spell — a control
character — is a compile error.) `ni` and its negations lower verbatim
(`a ni b`, `a !ni b`); the engine owns their semantics.

## Raw Lean selectors

`lean (f)` selects by running an ordinary Lean function over the values the
relationalizer walked, rather than by querying the relational encoding:

```lean
hideAtom      lean (fun n : RBNode => n matches .nil)
inferredEdge  kids lean (fun p c : RBNode => (p.children).contains c)
```

`f` must be closed and non-dependent. The contract (`SpytialLean/Sel.lean`) is
`Spytial.Sel T α`, a structure wrapping `T → Spytial.Tuples α`: a plain
function of the value being drawn, returning the selected tuples of values,
read as a set. `f`'s type says which form it is:

| `f` | arity | meaning |
|-----|-------|---------|
| `σ₁ → ⋯ → σₙ → Bool` (or `Prop`, via `Decidable`) | n | one decision per point of the product |
| `Spytial.Sel T α` | columns of `α` | called on the datum, selecting exactly what it returns |

Resolution runs against the value being drawn (an attached `spytial_spec`
stores `f` and resolves it once per value): the walked values of each column
are quoted into one term, and the term runs through the compiled evaluator —
the same machinery as `#eval`, so a definition from another module must be
`meta import`ed, and `whnf` never touches user code. The selector rewrites to
the tuples it selected — `` `a1->`a2->`a3 + `a4->`a5->`a6 ``, which the engine
resolves by atom id — or `none` when nothing matches. At most 4 columns; at
most 4096 selected tuples.

Selection is by *value*, and by default the walk keys atoms by value too
(structural identity, derived on demand), so a selected value selects exactly
one atom; under `SpytialIdentity.asWritten` it selects every occurrence.
A `Sel`'s returned values are located by `==`, so each of its column types
needs `BEq`; predicates return nothing and need no instance.
A `Sel` is ordinary computable code — build it with the anonymous constructor
(`⟨fun root => …⟩`), walk your own type inside it, test it with `#eval`. When
the *position* matters rather than the value, that is the relational
language's job (`left`, `right`, field names).

`lean` reaches values, not the diagram, so it cannot name a group or an inferred
edge introduced by an earlier op, and it cannot name a relation the walker
synthesizes. Those stay in the relational language, which composes with it:
`hideAtom lean (p) + Color` is one selector.

A resolved `lean (f)` is a list of atom ids, which says nothing to a reader of
a conflict report, so the ops core cites in one also carry the source they were
written as (`source.text`/`source.location`; `spytial.source`, on by default).
Core cites that in place of its own rendering of the rule.

[lean-selectors.md](lean-selectors.md) is the user-facing guide: how to use it,
which shape to pick, what does not work, and what each error means.

## What gets checked

The elaborator computes the target type's **data vocabulary**: the reachable
closure of type sigs, field-relation names, and nullary-constructor labels
that the relationalizer can emit. It checks every identifier and every
operator's operand width against this vocabulary; the widths are the
manifest's `accepts` — the column counts each op position takes — measured
against the engine rather than transcribed. `hideAtom` and `atomStyle` select
atoms (arity 1), so `hideAtom left` is a compile error. `orientation` and
`align` take two columns or more, keeping the first and the last.
`inferredEdge` takes two or more, drawing the first column to the last and
folding the columns between into the edge label — or one, when `draw` says
where the single atom's other end goes.

Each accepted form also says what the engine does with the columns between a
tuple's first and last. Where it discards them, a selector wider than two
columns warns: `orientation tr below` on a ternary `tr` draws the first atom
to the third and the middle one is not read. Where it shows them —
`inferredEdge`, which folds them into the edge label, and `tag`, which uses
them as key segments — a wide selector is doing what the position is for, and
there is no warning.

A group name or an inferred-edge name introduced by an earlier op lives in the
drawn graph, which the engine never queries: naming one in a *selector*
warns. In a *field-name* position it depends on the position, which the
manifest states — `edgeStyle hop` resolves the inferred edge `hop`, while
`hideField hop` and `attribute hop` match before that edge exists and warn.

Checking is **strict** exactly when the vocabulary is closed: a monomorphic
type built from monomorphic fields. A type parameter, a function field that
does not tabulate, or a custom relationalizer makes the scope lenient. Unknown names then warn,
and resolved types (like `Nat` in a `Tree α` spec) pass without a warning.

Derived type and field names are **short names** (`T` for `A.T`, `left` for a
`left` field), a convention shared with the Rust and Python Spytial
implementations. At render time a selector like `hideField left` matches
every relation with that short name, so two constructors that each have a
`left` field are styled together. The checker resolves one specific
declaration, so on a short-name collision the runtime matches more than the
checker points at.

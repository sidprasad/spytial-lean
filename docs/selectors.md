# The selector language

Selectors replicate Forge's relational expression/formula grammar, embedded as
Lean syntax (categories `spytial_sel` and `spytial_sel_form`, declared in
`SpytialLean/SelectorElab.lean`). This file is the language reference; the op
positions that accept selectors are listed in the README.

## Grammar

Tiers bind tighter downward; the numbers are the precedence levels in the
source. Binary operators are left-associative except `implies`. The grammar is
untyped — the relational/integer/value split ("Typing" below) is enforced by
the elaborator, not the parser.

```ebnf
(* expressions — spytial_sel *)
sel ::=
    "sum" ident ":" sel "|" sel                  (*  5: aggregation quantifier; integer *)
  | sel "+" sel | sel "-" sel                    (* 30: union, difference *)
  | "#" sel                                      (* 34: cardinality; integer *)
  | sel "++" sel                                 (* 36: override *)
  | sel "&" sel                                  (* 40: intersection *)
  | sel [mult] "->" [mult] sel                   (* 50: product *)
  | sel "<:" sel | sel ":>" sel                  (* 55: domain / range restriction *)
  | sel "." sel                                  (* 60: join *)
  | sel "[" sel ("," sel)* "]"                   (* 60: box join, a[b] ≡ b.a *)
  | "^" sel | "*" sel | "~" sel                  (* 70: closures, transpose *)
  | "@:" sel | "@str:" sel | "@bool:" sel        (* 100: label projections; value *)
  | "@num:" sel                                  (* 100: numeric projection; integer *)
  | ident                                        (* relation, sig, binder, or ctor label *)
  | "univ" | "iden" | "none"
  | "{" binders "|" form "}"                     (* comprehension; arity = #binders *)
  | "(" sel ")"
  | string                                       (* escape hatch / string literal *)
  | int                                          (* integer literal *)
  | "`" name                                     (* atom literal, a Lean name literal *)
  | "lean" "(" term ")"                          (* Lean selector; arity 1–4 *)

mult ::= "lone" | "one" | "some" | "set"

binders ::= group ("," group)*
group   ::= ident ("," ident)* ":" sel

(* formulas — spytial_sel_form *)
form ::=
    quantifier ["disj"] binders "|" form         (*  5 *)
  | "let" letBinds "|" form                      (*  5: desugars by substitution *)
  | form ("||" | "or") form                      (* 10 *)
  | form "xor" form                              (* 13 *)
  | form ("<=>" | "iff") form                    (* 16 *)
  | form ("=>" | "implies") form ["else" form]   (* 20: right-associative *)
  | form ("&&" | "and") form                     (* 30 *)
  | ("!" | "not") form                           (* 40 *)
  | sel cmp sel                                  (* 50 *)
  | quantifier sel                               (* 60: multiplicity *)
  | "(" form ")"

letBinds ::= ident "=" sel ("," ident "=" sel)*
quantifier ::= "all" | "no" | "some" | "lone" | "one"
cmp ::= "=" | "!=" | "in" | "!in" | "not in" | "ni" | "!ni" | "not ni"
      | "<" | ">" | "<=" | ">=" | "=<"           (* integer comparisons; "=<" ≡ "<=" *)
```

The precedence is Forge's: implication binds tighter than `or` and `iff`
(`a || b => c` is `a || (b => c)`), and implication is the only
right-associative connective. Longest-match separates the quantifier
`some x : A | φ` from the multiplicity `some e`, whose operand extends down
through union (`some A + B` is `some (A + B)`). Whitespace matters twice: no
space before a box-join `[`, and none between `-` and an integer literal. A
string is the raw, unchecked SGQ escape hatch as a whole selector, and an
ordinary string literal as a comparison operand.

An identifier is a single component. The selector lexer stops at a `.`, so the
dot is always the join operator and `a.b` and `a . b` are the same selector,
read as SGQ reads them — spacing carries no meaning, and a unary operator binds
tighter (`^a.b` is `(^a).b`). A name that must contain a dot, or one that
collides with a keyword, is escaped with guillemets: `«Untyped.Term»` for a
qualified Lean type, `«univ»` for a field named after a nullary constant.

Relative to Forge, the label projections (`@:`, `@str:`, `@bool:`, `@num:`)
and the raw-string escape hatch are SGQ/Spytial extensions, and atom literals
are spelled as Lean name literals (`` `a0 ``). The fragment omits Forge's
declaration and temporal layers. Arrow multiplicities (`A one -> lone B`)
parse for grammar parity, but the engine rejects them at render: they are
declaration and constraint syntax, not part of an expression.

## Meaning

| Form | Meaning |
|------|---------|
| `left`, `app_0` | a field relation (arity 2: parent → child) |
| `RBNode`, `String` | a type sig (arity 1: all atoms of that type) |
| `a[b, …]` | box join (`a[b] ≡ b.a`) |
| `{x, y : T \| φ}` | set comprehension (arity = number of binders) |
| `@:e`, `@str:e`, `@bool:e` | label projections (string/bool value reads) |
| `univ`, `iden` | the universe and identity relations |
| `lean (f)` | the tuples the Lean function `f` selects (arity from `f`'s type) |

**`let x = e, … | φ`** desugars by substitution at elaboration; the engine
never sees a `let`. A later binder shadows the `let`. A substitution that an
inner binder would capture is a compile error.

## Typing

The elaborator types every expression as relational, integer, or value; each
position accepts specific kinds, so SGQ's silent scalar/tuple confusion
(`some #e`) is a compile error.

**Integer layer.** The integer forms are: `#e` (cardinality), integer
literals, `@num:e` (numeric projection), the builtins `add subtract multiply
divide remainder abs sign`, the aggregators `sum[e]`, `min[e]`, and `max[e]`
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

## Lean selectors

`lean (f)` selects atoms or tuples from the refined, relationalized datum.
Each candidate must have a represented Lean term of the corresponding
argument type. The surrounding inspection supplies available information;
it does not change the selector language.

```lean
hideAtom      lean (fun n : RBNode => n matches .nil)
inferredEdge  kids lean (fun p c : RBNode => (p.children).contains c)
```

The function type determines the form and arity:

| `f` | arity | meaning |
|-----|-------|---------|
| `σ₁ → ⋯ → σₙ → Bool` or `Prop` | n | represented tuples whose predicate is established |
| `Spytial.Sel T α` | columns of `α` | execute on the root, locate returned values in the datum |

Predicates have one to four non-dependent arguments and may capture local
parameters. Closed predicates on closed values use compiled evaluation
(`Decidable` for propositions). Otherwise direct proof matching and bounded
simplification use the retained context facts and checked observation
equations. No `Decidable` instance is required for this proof-backed path.
Both command mode and tactic mode use the same resolver, including predicates
stored in an attached `spytial_spec`.

A `Spytial.Sel` remains closed executable code over a fully determined root.
Returned values are located by `BEq`; it needs that instance for each column.
An incomplete root remains an explicit error, even in an attached spec.
This does not silently replace a required selector with an empty selection.

Predicates inspect the represented value, not just its display label or
identity key. A coarser identity classifier does not establish Lean equality
between merged values; resolution uses the drawn representative and
established aliases. Under `SpytialIdentity.asWritten`, equal values remain
separate atoms and a matching predicate selects each occurrence.

Resolution rewrites `lean (f)` to atom tuples, such as
`` `a1->`a2 + `a3->`a4 ``, or `none` when no matches are established.
Missing evidence is not a proof of negation: `lean (fun x => ¬ P x)` requires
support for the negation. Relational difference `univ - lean (P)` is ordinary
set subtraction and includes undetermined cases.

Selection never adds atoms or facts to the datum. Synthetic atoms without
Lean terms, group names, and invented relation names remain the relational
language's domain. The two styles compose: `hideAtom lean (p) + Color`.

At most 4,096 tuples can be selected. Compiled enumeration is capped at one
million points; symbolic candidate/evidence checks have the same bound.
Simplification is bounded to 1,000 steps per check. Limit failures are errors,
not partial selections. Compiled imports must be available via `meta import`;
symbolic unfolding requires accessible definitions or suitable lemmas.

A resolved selector carries its original source text and location
(`spytial.source`, on by default), so a conflict report cites the user's
predicate rather than only generated atom IDs.

[lean-selectors.md](lean-selectors.md) provides examples, the reasoning
contract, and limitations.

## What gets checked

The elaborator computes the target type's **data vocabulary**: the reachable
closure of type sigs, field-relation names, and nullary-constructor labels
that the relationalizer can emit. It checks every identifier and every
operator's arity against this vocabulary. Op positions have arity
expectations: `hideAtom` and `atomStyle` select atoms (arity 1),
`orientation` and `align` select pairs. `hideAtom left` is a compile error.
A wider selector in a pair position warns, because the engine keeps only the
first and last column there. `inferredEdge` takes any arity from 2 up without
a warning: it draws the first column to the last and folds the columns
between them into the edge label.

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

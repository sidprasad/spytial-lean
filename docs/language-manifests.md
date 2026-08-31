# The language manifests

The two surface languages this package accepts are defined elsewhere:

- selectors are simple-graph-query's expression language, published as
  `docs/sgq-language.json` in that package;
- the op surface is spytial-core's layout-spec language, published as
  `docs/spytial-language.json` in that package.

`SpytialLean.Sgq` and `SpytialLean.SpecLang` parse the resolved copies and
declare id enumerations and tables. The parser, the elaborator and the
lowering read those tables and name no construct, item or field, so a
construct or field added upstream reaches all three by rebuilding against the
bumped dependency. Before the manifests, both languages were mirrored by hand
and the mirrors drifted: `sgqReserved` still listed ten keywords sgq had
deleted, and nothing could have caught it.

## Decoding

Records mirror the manifests and decode with `deriving FromJson`, whose errors
name the member that moved. Tagged shapes use `json_union`
(`SpytialLean.ManifestJson`), which declares an inductive and its decoder from
one list, so a constructor and its JSON spelling cannot drift apart. A tag,
enum value, or renamed member with no representation stops the build naming
the construct or item, rather than yielding a plausible table. One drift class
passes: `deriving FromJson` ignores members it does not know, so a member
*added* upstream is silently unread until something else fails. Core 5.4.0 grew
two — `accepts` on selector fields and the `source` block — and neither
announced itself.

## What is not the manifests'

House style is this package's own and lives beside the tables it refines:
which spelling to emit where the engine accepts several
(`preferredSpelling`), whitespace (`Selector.lean`), and how manifest fields
lay out as Lean arguments (`SpecLang.lean`'s house-style tables, now the
leading-selector override and the bare-word bool sugar). Every table entry is
keyed by manifest ids and checked against the live manifest, so an entry that
stops matching upstream fails the build by name.

Three more facts were house tables here and are core's own members now.
`introduces` gives the string field that names a group or an inferred edge,
how many columns that thing has, and the `item.field` positions where the
engine resolves such a name — which is what lets a reference from any other
field position warn instead of passing silently. `inertWhenBare` marks the
items whose whole effect is their optional presentation fields; which fields
those are is the member's own prose rule (optional, and not of type `selector`
or `relation`), applied in `itemOf`. `middleColumns` says what an accepted
form does with the columns between a tuple's first and last, which separates a
wide selector that is throwing information away from one that is not; a form
admitting a third column and declaring nothing is a derivation error naming
the field.

Deprecated items and fields get no surface: the Lean DSL is new and has no
legacy specs to keep parsing. `deprecatedItems` and `deprecatedFields` record
what was declined, by name.

## Build integration

Both manifests are read while `Sgq.lean` and `SpecLang.lean` elaborate
(`include_str`), which Lean's import graph does not see; the lakefile names
them as `input_file`s the library needs, so a dependency bump re-elaborates
the modules. The SGQ manifest ships with simple-graph-query#68, which is
unpublished; until it lands, `pnpm-workspace.yaml` overrides the package to a
local checkout.

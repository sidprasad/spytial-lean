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

Records mirror the manifests and decode through two commands in
`SpytialLean.ManifestJson`, each declaring a reader from one statement so a
shape and its decoder cannot drift apart. Tagged shapes use `json_union`: an
inductive and its decoder from one list, pairing each constructor with its
JSON spelling. Records use `json_record`: the decoder is read off the
structure's own fields, and it is closed — a member outside the field list
stops the build naming it, so a member *added* upstream announces itself
instead of being silently unread. (That class had already bitten: core 5.4.0
grew `accepts` and the `source` block, and neither announced itself.) A member
known and deliberately unread is declared in the command's `ignoring` list; two
readers sharing one object (`JField`, `JFieldType`) share member lists the same
way. A tag, enum value, or renamed member with no representation stops the
build naming the construct or item, rather than yielding a plausible table.

## Version pin

The spytial-core manifest has no version over its own member shape, only
`languageVersion`, the date the language last changed. The tables in
`SpecLang.lean` that stand in for members the manifest lacks (below) hold for
one language, so `tablesLanguageVersion` states the `languageVersion` they
were audited against and derivation fails on any other, naming both dates. A
language change is exactly when a table can go stale, and nothing else would
say so. The SGQ manifest has no equivalent member either; its `sgqVersion` is
the package's version, not the file's shape.

## What is not the manifests'

Some choices are this package's own and live beside the tables they refine:
which spelling to emit where the engine accepts several
(`preferredSpelling`), whitespace (`Selector.lean`), and how manifest fields
lay out as Lean arguments (`SpecLang.lean`'s leading-selector override and
bare-word bool sugar). Every table entry is keyed by manifest ids and
checked against the live manifest, so an entry that stops matching upstream
fails the build by name.

Three facts the manifest does not carry are tables beside it, proposed
upstream as spytial-core#580 and #581 and kept here until a release carries
them. `introducesTable` gives the string field that names a group or an
inferred edge, which kind it names (`introducedKindsTable` says how many
columns each kind has), and the `item.field` positions where the engine
resolves such a name — which is what lets a reference from any other field
position warn instead of passing silently. `inertWhenBareTable` names the
fields that are an item's whole effect, so a body setting none of them is
rejected at elaboration. `middleColumnsTable` says what the engine does with
the columns between a wide tuple's first and last, per selector position that
admits more than two, which separates a wide selector that is throwing
information away from one that is not. Each entry is checked against the live
manifest both ways: an entry naming a position the manifest lacks, and a wide
position the table does not cover, are derivation errors naming the field.

Deprecated items and fields get no surface: the Lean DSL is new and has no
legacy specs to keep parsing. `deprecatedItems` and `deprecatedFields` record
what was declined, by name.

## Build integration

Both manifests are read while `Sgq.lean` and `SpecLang.lean` elaborate
(`include_str`), which Lean's import graph does not see; the lakefile traces
them as targets the library needs — sequenced after the pnpm install that
creates them, so a fresh checkout builds first try — and a dependency bump
re-elaborates the modules.

simple-graph-query is overridden to a local checkout in
`pnpm-workspace.yaml`, because its manifest ships with simple-graph-query#68,
which is unpublished. Drop the override when a release carries the file, and
the package.json pin takes over. spytial-core resolves to its published 5.4.0.

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

## Format versioning

The spytial-core manifest carries `manifestVersion`, a semver over the file's
own member shape: which members exist and what they mean. A consumer requires
the minor that introduced each member it reads, so `SpecLang.lean` states the
pair it needs (`neededMajor`/`neededMinor`, 1.1 for `introducedKinds`) and
checks it before decoding the record — a manifest too old to carry a member
then says so instead of failing by that member's name. An absent
`manifestVersion` means the file predates format versioning. Either message
gives the version found and the version needed.

The check is one-sided, which is what a per-member requirement means: a
manifest ahead of this reader still decodes, because what it grew is what
nothing here reads yet. That is the drift class above, and the version does
not close it. The SGQ manifest has no equivalent member; its `sgqVersion` is
the package's version, not the file's shape.

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
which of those kinds it names, and the `item.field` positions where the engine
resolves such a name — which is what lets a reference from any other field
position warn instead of passing silently. How many columns a kind has is
`introducedKinds`, so group-is-one and edge-is-two are read rather than
restated here, and a kind that is not one of its keys is a derivation error
naming the field. `inertWhenBare` names the fields that are an item's whole
effect, so nothing here reapplies a rule for which ones count; `itemOf` checks
each named field against the item and rejects a marked item that names none.
Absence of the member is indistinguishable from "not inert", so a manifest
where no item declares it is a derivation error too, rather than a check that
quietly stops running. `middleColumns` says what an accepted form does with
the columns between a tuple's first and last, which separates a wide selector
that is throwing information away from one that is not; a form admitting a
third column and declaring nothing is a derivation error naming the field.

Deprecated items and fields get no surface: the Lean DSL is new and has no
legacy specs to keep parsing. `deprecatedItems` and `deprecatedFields` record
what was declined, by name.

## Build integration

Both manifests are read while `Sgq.lean` and `SpecLang.lean` elaborate
(`include_str`), which Lean's import graph does not see; the lakefile names
them as `input_file`s the library needs, so a dependency bump re-elaborates
the modules.

Both packages are overridden to a local checkout in `pnpm-workspace.yaml`,
because both manifests are ahead of their releases. The SGQ manifest ships
with simple-graph-query#68, which is unpublished. `manifestVersion`,
`introducedKinds`, `introduces`, `inertWhenBare` and `middleColumns` ship with
spytial-core#580/#581, and the override points at a built checkout of the two
merged; published 5.4.0 carries none of them and now stops the build at the
format check, reporting the absent `manifestVersion`. Drop each override when
a release carries its manifest, and the package.json pins take over.

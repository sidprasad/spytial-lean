module

public import Lean.Elab.Command
meta import SpytialLean.Command

open SpytialLean Lean Elab Command

-- These goldens pin the op surface, not the source stamp, so they leave the
-- stamp out rather than restate it on every op. It has its own tests, under
-- `## The source stamp` in LeanSelectorTest.
set_option spytial.source false

/-! # Tests for the manifest-driven op surface

`SelectorTest.lean` pins the pre-rewrite battery byte-for-byte; this file
covers what only the tables carry — hold, textStyle at every site, directive
scoping (`selector:`/`filter:`), `draw`, `hidden`, opacity, nested block
keywords, and the manifest's own validity rules (list rules, numeric bounds,
enum membership). Each negative test is a detector's positive control. -/

/-! ## Fixture -/

public inductive SG where
  | leaf
  | node (tag : String) (lo hi : SG)

public def sG : SG := .node "r" .leaf .leaf

/-! ## Hold -/

/--
info: {"constraints":
 [{"orientation":
   {"selector": "lo", "hold": "never", "directions": ["below"]}}]}
-/
#guard_msgs in
#spytial.spec sG with [orientation lo below hold: never]

-- `always` is inert upstream but written is emitted: the serialized spec
-- carries what the source said.
/-- info: {"constraints": [{"cyclic": {"selector": "lo", "hold": "always"}}]} -/
#guard_msgs in
#spytial.spec sG with [cyclic lo hold: always]

/-- error: hideAtom does not support hold; usage: hideAtom <selector> -/
#guard_msgs in
#spytial.spec sG with [hideAtom SG hold: never]

/-- error: unknown hold 'sometimes' (expected always, never) -/
#guard_msgs in
#spytial.spec sG with [orientation lo below hold: sometimes]

/-! ## textStyle, at sites the old surface lacked -/

/--
info: {"directives":
 [{"atomStyle":
   {"textStyle": {"size": "small", "color": "gray"}, "selector": "SG"}}]}
-/
#guard_msgs in
#spytial.spec sG with [atomStyle SG (textStyle "gray" small)]

/--
info: {"directives":
 [{"attribute":
   {"textStyle": {"size": "small"}, "selector": "SG", "field": "tag"}}]}
-/
#guard_msgs in
#spytial.spec sG with [attribute tag selector: SG (textStyle small)]

/--
info: {"constraints":
 [{"group": {"textStyle": {"color": "green"}, "selector": "SG", "name": "g"}}]}
-/
#guard_msgs in
#spytial.spec sG with [group SG g (textStyle "green")]

/-! ## Directive scoping and edge knobs -/

/--
info: {"directives":
 [{"edgeStyle":
   {"textStyle": {"size": "large"},
    "showLabel": false,
    "selector": "SG",
    "lineStyle": {"highlight": "yellow", "color": "red"},
    "hidden": true,
    "filter": "lo.hi",
    "field": "lo"}}]}
-/
#guard_msgs in
#spytial.spec sG with [edgeStyle lo selector: SG filter: (lo.hi)
  (lineStyle "red" (highlight "yellow")) (textStyle large)
  showLabel: false hidden: true]

/-- info: {"directives": [{"hideField": {"filter": "lo", "field": "lo"}}]} -/
#guard_msgs in
#spytial.spec sG with [hideField lo filter: lo]

/-! ## inferredEdge draw -/

/--
info: {"directives":
 [{"inferredEdge":
   {"textStyle": {"color": "blue"},
    "selector": "lo",
    "name": "hop",
    "draw": "_ -> cluster"}}],
 "constraints": [{"group": {"selector": "SG", "name": "cluster"}}]}
-/
#guard_msgs in
#spytial.spec sG with [group SG cluster,
  inferredEdge hop lo draw: "_ -> cluster" (textStyle "blue")]

/-! ## tag's value is a checked selector -/

/--
info: {"directives":
 [{"tag":
   {"value": "lo.hi",
    "toTag": "SG",
    "textStyle": {"color": "gray"},
    "name": "kids"}}]}
-/
#guard_msgs in
#spytial.spec sG with [tag SG "kids" lo.hi (textStyle "gray")]

/-- error: a selector picks out atoms or tuples, but this is an integer expression -/
#guard_msgs in
#spytial.spec sG with [tag SG "n" #lo]

-- A tag's value shows its middle columns as key segments, so a wide one is not
-- throwing anything away and must not warn.
/-- info: {"directives": [{"tag": {"value": "lo->hi", "toTag": "SG", "name": "kids"}}]} -/
#guard_msgs in
#spytial.spec sG with [tag SG "kids" (lo->hi)]

/-! ## size: width and height required, selector optional -/

/-- info: {"constraints": [{"size": {"width": 150, "height": 80}}]} -/
#guard_msgs in
#spytial.spec sG with [size 150 80]

/-- error: missing height; usage: size [<selector>] <width> <height> -/
#guard_msgs in
#spytial.spec sG with [size SG 100]

/-- error: width must be greater than 0 -/
#guard_msgs in
#spytial.spec sG with [size 0 80]

/-! ## atomStyle without a selector styles every atom -/

/-- info: {"directives": [{"atomStyle": {"fillStyle": {"color": "red"}}}]} -/
#guard_msgs in
#spytial.spec sG with [atomStyle (fillStyle "red")]

/-! ## Blocks: nested keywords, opacity, pathless icons -/

/--
info: {"directives":
 [{"atomStyle":
   {"selector": "SG", "iconStyle": {"placement": "badge", "opacity": 0.5}}}]}
-/
#guard_msgs in
#spytial.spec sG with [atomStyle SG (iconStyle badge (opacity 0.5))]

/-- info: {"directives": [{"atomStyle": {"selector": "SG", "borderStyle": {"width": 3}}}]} -/
#guard_msgs in
#spytial.spec sG with [atomStyle SG (borderStyle (width 3))]

/-- error: opacity must be at most 1 -/
#guard_msgs in
#spytial.spec sG with [atomStyle SG (iconStyle (opacity 1.5))]

/-! ## addEdge: bare enum vs block form -/

/--
info: {"constraints":
 [{"group":
   {"selector": "SG",
    "name": "g",
    "addEdge":
    {"textStyle": {"color": "blue"},
     "points": "fromgroup",
     "lineStyle": {"color": "red"}}}}]}
-/
#guard_msgs in
#spytial.spec sG with [group SG g (addEdge fromgroup (lineStyle "red") (textStyle "blue"))]

/-- error: (addEdge …) needs a direction (none, togroup, fromgroup) -/
#guard_msgs in
#spytial.spec sG with [group SG g (addEdge (lineStyle "red"))]

/-! ## Keyword form of an optional enum -/

/--
info: {"constraints":
 [{"cyclic": {"selector": "lo", "direction": "counterclockwise"}}]}
-/
#guard_msgs in
#spytial.spec sG with [cyclic lo direction: counterclockwise]

/-- error: 'direction' is a positional argument; usage: align <selector> horizontal|vertical [hold: always|never] -/
#guard_msgs in
#spytial.spec sG with [align lo direction: horizontal]

/-! ## The manifest's list rules -/

/-- error: directions allows at most one of above|below, got above, below -/
#guard_msgs in
#spytial.spec sG with [orientation lo above below]

/-- error: 'directlyAbove' restricts directions to above|directlyAbove; 'left' cannot join it -/
#guard_msgs in
#spytial.spec sG with [orientation lo directlyAbove left]

/-- error: duplicate directions 'above' -/
#guard_msgs in
#spytial.spec sG with [orientation lo above above]

/-! ## Vocabulary errors -/

/--
error: unknown keyword 'foo:'; usage: orientation <selector> <directions>+ [hold: always|never]
-/
#guard_msgs in
#spytial.spec sG with [orientation lo below foo: bar]

/-- error: unknown flag 'whatever' (expected hideDisconnected, hideDisconnectedBuiltIns) -/
#guard_msgs in
#spytial.spec sG with [flag whatever]

/--
error: edgeStyle sets nothing; usage: edgeStyle <field> [selector: <selector>] [filter: <selector>] [(lineStyle …)] [(textStyle …)] [labels|noLabels] [hidden: true|false]
-/
#guard_msgs in
#spytial.spec sG with [edgeStyle lo]

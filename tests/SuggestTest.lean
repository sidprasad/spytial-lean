module

public meta import SpytialLean

open SpytialLean

/-! Golden tests for `#spytial.suggest`.

The two red-black tree cases pin the whole message, because they pin the part
that is subtle: which spelling of a name resolves from where the block will be
pasted. The rest assert only that no warning is produced — a warning from
`#spytial.suggest` means a rule proposed an op that does not check, which is
the failure that matters and the one immune to rewording a rationale. -/

namespace SuggestFixture

public inductive Color where
  | red | black

/-- The canonical case: the README's red-black tree, from the declaration alone. -/
public inductive RBNode where
  | nil : RBNode
  | node (color : Color) (key : Nat) (left : RBNode) (right : RBNode) : RBNode

/-- A recursive back pointer next to a forward edge. -/
public inductive Employee where
  | mk (name : String) (reports : Employee) (parent : Employee)

/-- Three recursive fields: no horizontal order generalizes, so all fan down. -/
public inductive Rose where
  | node (label : String) (kids : Rose) (sibling : Rose) (extra : Rose)

/-- Nothing to say: an enumeration has no fields to lay out. -/
public inductive Flag where
  | on | off

/-- A type parameter is unpredictable statically, so `contents` is skipped. -/
public inductive Box (α : Type) where
  | mk (contents : α) (next : Box α)

/-- A field named after a selector keyword still has to be spellable. -/
public inductive Odd where
  | mk (univ : Nat) (next : Odd)

/--
info: Try this:
  [apply] spytial_spec SuggestFixture.RBNode [
    attribute color,
    attribute key,
    orientation left left below,
    orientation right right below,
    hideAtom Color + Nat,
    atomStyle {x : RBNode | @:(x.color) = red} (borderStyle "red"),
    atomStyle {x : RBNode | @:(x.color) = black} (borderStyle "black")
  ]
• attribute color — 'color' is the enumeration Color — fold it into the node
• attribute key — 'key' is a Nat — read it on the node, not as an edge
• orientation left left below — 'left' is the left child of a binary node
• orientation right right below — 'right' is the right child of a binary node
• hideAtom Color + Nat — Color + Nat now reads as labels, so the separate atoms are duplicates
• atomStyle {x : RBNode | @:(x.color) = red} (borderStyle "red") — 'color' enumerates colour names — draw 'red' as the border
• atomStyle {x : RBNode | @:(x.color) = black} (borderStyle "black") — 'color' enumerates colour names — draw 'black' as the border

A draft, not an answer — edit it.
-/
#guard_msgs(info, drop warning) in
#spytial.suggest RBNode

#guard_msgs(drop info) in
#spytial.suggest Employee

#guard_msgs(drop info) in
#spytial.suggest Rose

#guard_msgs(drop info) in
#spytial.suggest Flag

#guard_msgs(drop info) in
#spytial.suggest Box

#guard_msgs(drop info) in
#spytial.suggest Odd

end SuggestFixture

/-! Outside the namespace the short spellings no longer resolve, so the
    qualified fallback is what gets offered. Relation names are unaffected:
    they are vocabulary, not Lean names. -/

/--
info: Try this:
  [apply] spytial_spec SuggestFixture.RBNode [
    attribute color,
    attribute key,
    orientation left left below,
    orientation right right below,
    hideAtom «SuggestFixture.Color» + Nat,
    atomStyle {x : «SuggestFixture.RBNode» | @:(x.color) = «SuggestFixture.Color.red»} (borderStyle "red"),
    atomStyle {x : «SuggestFixture.RBNode» | @:(x.color) = «SuggestFixture.Color.black»} (borderStyle "black")
  ]
• attribute color — 'color' is the enumeration Color — fold it into the node
• attribute key — 'key' is a Nat — read it on the node, not as an edge
• orientation left left below — 'left' is the left child of a binary node
• orientation right right below — 'right' is the right child of a binary node
• hideAtom «SuggestFixture.Color» + Nat — Color + Nat now reads as labels, so the separate atoms are duplicates
• atomStyle {x : «SuggestFixture.RBNode» | @:(x.color) = «SuggestFixture.Color.red»} (borderStyle "red") — 'color' enumerates colour names — draw 'red' as the border
• atomStyle {x : «SuggestFixture.RBNode» | @:(x.color) = «SuggestFixture.Color.black»} (borderStyle "black") — 'color' enumerates colour names — draw 'black' as the border

A draft, not an answer — edit it.
-/
#guard_msgs(info, drop warning) in
#spytial.suggest SuggestFixture.RBNode

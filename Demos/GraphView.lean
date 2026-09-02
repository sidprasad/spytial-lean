import SpytialLean

open SpytialLean

/-! # Drawing a graph as a graph — with declarations, not hand emission

A `SimpleGraph` value is two lists, and the generic walk would draw the cons
cells. The picture we want — one node per vertex, one edge per pair, however
many lists mention the vertex — is a *description* of the type, so it is
declared: `Rel` makes the edge list a relation instead of a child chain, and
`SpytialIdentity` makes equal vertices one atom, which is what wires an edge's
endpoints to the vertex nodes. (This demo used to hand-emit all of that
through a custom relationalizer, at ~60 lines of cons-chain walking.) -/

structure Vertex where
  name : Hidden String

instance : SpytialIdentity Vertex := ⟨.identity fun v => .ofString v.name.val, none⟩

instance : SpytialDisplay Vertex := ⟨fun v => v.name.val⟩

structure SimpleGraph where
  vertices : Rel Vertex
  edges : Rel (Vertex × Vertex)

/-- The wrappers have no `ToIdentityKey` encoding (yet), so nothing derives;
    one graph value has nothing to merge with anyway. -/
instance : SpytialIdentity SimpleGraph := .asWritten

-- The datum records ownership — `edges ⊆ SimpleGraph × Vertex × Vertex` —
-- and the *display* projects it away: vertex→vertex arrows, not a fan from
-- the graph node.
spytial_spec SimpleGraph [
  inferredEdge edge univ . (edges),
  hideField edges
]

def myGraph : SimpleGraph where
  vertices := ⟨[⟨⟨"A"⟩⟩, ⟨⟨"B"⟩⟩, ⟨⟨"C"⟩⟩, ⟨⟨"D"⟩⟩]⟩
  edges := ⟨[(⟨⟨"A"⟩⟩, ⟨⟨"B"⟩⟩), (⟨⟨"B"⟩⟩, ⟨⟨"C"⟩⟩), (⟨⟨"C"⟩⟩, ⟨⟨"A"⟩⟩), (⟨⟨"A"⟩⟩, ⟨⟨"D"⟩⟩)]⟩

-- 4 vertex nodes, 4 directed edges, no internal List structure
#spytial myGraph
#spytial.datum myGraph

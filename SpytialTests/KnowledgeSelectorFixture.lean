module

public import SpytialLean

public inductive KnowledgeTree where
  | leaf
  | node (left right : KnowledgeTree)
  deriving BEq

@[expose] public def KnowledgeTree.height : KnowledgeTree → Nat
  | .leaf => 0
  | .node left right => max left.height right.height + 1

@[expose] public def threeHigh : KnowledgeTree :=
  .node (.node (.node .leaf .leaf) .leaf) .leaf

@[expose] public def hasHeightThree (n : KnowledgeTree) : Prop := n.height = 3

-- Serialized into an .olean and resolved in the importing proof's context.
set_option spytial.source false in
spytial_spec KnowledgeTree [hideAtom lean (hasHeightThree)]

module

public import SpytialLean

public inductive KnowledgeTree where
  | leaf
  | node (left right : KnowledgeTree)
  deriving BEq

public def KnowledgeTree.height : KnowledgeTree → Nat
  | .leaf => 0
  | .node left right => max left.height right.height + 1

-- Serialized into an .olean and resolved in the importing proof's context.
set_option spytial.source false in
spytial_spec KnowledgeTree [hideAtom known (fun n : KnowledgeTree => n.height = 3)]

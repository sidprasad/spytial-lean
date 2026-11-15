import SpytialLean
import CLRSLean.FourthEdition.Chapter_13.Section_13_1_Red_Black_Trees

/-!
Type-attached annotations for CLRS-Lean's original red-black tree, following
the key labels, subtree ordering, and red/black styling in spytial-clrs/trees.ipynb.
Importing this module registers the default layout; the upstream datatype is unchanged.
-/

open SpytialLean CLRS.Chapter13

-- The upstream constructor has positional arguments: color, left, key, right.
-- Spytial exposes them as node_0, node_1, node_2, and node_3 respectively.
spytial_spec RBTree [
  orientation node_1.*(node_1 + node_3) &
    ((RBTree - lean (fun t : RBTree => t = .empty)) ->
      (RBTree - lean (fun t : RBTree => t = .empty))) left below,
  orientation node_3.*(node_1 + node_3) &
    ((RBTree - lean (fun t : RBTree => t = .empty)) ->
      (RBTree - lean (fun t : RBTree => t = .empty))) right below,
  align (~(node_1 + node_3).(node_1 + node_3) - iden) &
    ((RBTree - lean (fun t : RBTree => t = .empty)) ->
      (RBTree - lean (fun t : RBTree => t = .empty))) horizontal,
  attribute node_2,
  hideField node_0,
  hideAtom Color + Nat + lean (fun t : RBTree => t = .empty),
  edgeStyle node_1 noLabels,
  edgeStyle node_3 noLabels,
  size RBTree 56 42,
  atomStyle lean (fun t : RBTree => t.rootColor = .red)
    (borderStyle "#b91c1c" 2) (fillStyle "#fee2e2") (textStyle "#7f1d1d"),
  atomStyle lean (fun t : RBTree => t.rootColor = .black)
    (borderStyle "#111827" 3) (fillStyle "#f3f4f6") (textStyle "#111827")
]

namespace CLRSAnnotations

def sample : RBTree :=
  .node .black
    (.node .red (.node .black .empty 2 .empty) 4 (.node .black .empty 6 .empty))
    8
    (.node .red (.node .black .empty 10 .empty) 12 (.node .black .empty 14 .empty))

#spytial sample
#spytial_snapshot "annotated-red-black-tree" sample

end CLRSAnnotations

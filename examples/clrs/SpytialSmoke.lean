import SpytialLean
import CLRSLean.FourthEdition.Chapter_13.Section_13_1_Red_Black_Trees

/-! Exercise both concrete capture and proof-context inspection on an upstream datatype. -/

open SpytialLean CLRS.Chapter13

#spytial (RBTree.node .red .empty 1 (.node .red .empty 2 .empty))
#spytial_snapshot "red-black-tree" (RBTree.node .red .empty 1 (.node .red .empty 2 .empty))

example (a b c : RBTree) (x y : Nat)
    (ha : RBTree.RedBlackShape a) (hb : RBTree.RedBlackShape b)
    (hc : RBTree.RedBlackShape c)
    (hab : RBTree.blackHeight a = RBTree.blackHeight b)
    (hbc : RBTree.blackHeight b = RBTree.blackHeight c) :
    RBTree.RedBlackShape
      (RBTree.repaintRoot .black (RBTree.rotateLeft (.node .red a x (.node .red b y c)))) := by
  spytial (RBTree.node .red a x (.node .red b y c)) observing [RBTree.blackHeight]
  exact RBTree.redBlackShape_repaint_rotateLeft_red_red ha hb hc hab hbc

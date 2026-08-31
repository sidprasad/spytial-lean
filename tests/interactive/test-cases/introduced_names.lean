module

public import Lean.Elab.Command
public meta import SpytialLean.Attr
meta import SpytialLean.Command

open SpytialLean

set_option spytial.source false

inductive HBDD where
  | tt
  | ff
  | node (v : String) (lo hi : HBDD)

def hd : HBDD := .node "x" .tt .ff

#spytial.spec hd with [inferredEdge hop lo.hi, edgeStyle hop (lineStyle "purple")]
                                  --^ textDocument/hover
                                                       --^ textDocument/hover
                                                       --^ textDocument/definition

spytial_ops hgroups : HBDD [group HBDD cluster]
                                     --^ textDocument/hover

#spytial.spec hd with [..hgroups, edgeStyle cluster (lineStyle "red")]
                                          --^ textDocument/definition

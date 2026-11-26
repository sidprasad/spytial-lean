import Lean.Data.Lsp.Ipc
import Lean.Data.Lsp.InitShutdown
import Lean.Data.Lsp.Utf16

open Lean Lsp

namespace SpytialEditorTest

private def source := r##"import SpytialLean
inductive BDD where
  | fls
  | node (lo hi «univ» lean : BDD)
def ordinary := "#abcdef"
spytial_spec BDD [
  atomStyle {p : BDD | some q : BDD | q in p.lo && q in p.hi} (fillStyle "#ffe082"),
  atomStyle univ (borderStyle "#abc") (iconStyle "#123456"),
  edgeStyle lo (lineStyle "#0F08" (highlight "#10203040")),
  hideAtom univ.«univ» + univ.lean,
  hideAtom lean (fun n : BDD => (n matches .fls)) + BDD,
  atomStyle {x : BDD | @:x = fls} (fillStyle "#01x"),
  atomStyle BDD /- 🌳 -/ (textStyle (color "#FFFFFF"))
]
example : True ∧ True := by
  constructor <;> spytial_spec BDD [atomStyle BDD (fillStyle "#321")]
  all_goals trivial
"##

private def ask (id : Nat) (method : String) (params : α) [ToJson α]
    (β : Type) [FromJson β] : Ipc.IpcM β := do
  Ipc.writeRequest ⟨id, method, params⟩
  return (← Ipc.readResponseAs id β).result

private def slice (text : FileMap) (range : Lsp.Range) : String :=
  let r := text.lspRangeToUtf8Range range
  (Substring.Raw.mk text.source r.start r.stop).toString

private def decode (text : FileMap) (tokens : SemanticTokens) :
    Array (String × String × Nat) := Id.run do
  let mut pos : Lsp.Position := ⟨0, 0⟩
  let mut result := #[]
  let d := tokens.data
  for i in [0:d.size:5] do
    pos := ⟨pos.line + d[i]!, (if d[i]! == 0 then pos.character else 0) + d[i+1]!⟩
    let stop := { pos with character := pos.character + d[i+2]! }
    result := result.push (slice text ⟨pos, stop⟩, SemanticTokenType.names[d[i+3]!]!, pos.line)
  return result

private def sync (id : Nat) (uri : DocumentUri) (version : Nat) : Ipc.IpcM Unit := do
  if let some ds ← Ipc.collectDiagnostics id uri version then
    for d in ds.param.diagnostics do
      if d.severity? == some .error then throw <| IO.userError d.message

end SpytialEditorTest

open SpytialEditorTest in
def main : IO Unit := do
  let uri := System.Uri.pathToUri ((← IO.currentDir) / "SpytialTests" / "EditorExample.lean")
  let doc : TextDocumentIdentifier := ⟨uri⟩
  let text := FileMap.ofString source
  Ipc.runWith "lake" #["serve"] do
    let _ ← ask 0 "initialize" ({ capabilities := {} } : InitializeParams) InitializeResult
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
    Ipc.writeNotification ⟨"textDocument/didOpen",
      { textDocument := ⟨uri, "lean4", 1, source⟩ : DidOpenTextDocumentParams }⟩
    sync 1 uri 1
    let full ← ask 2 "textDocument/semanticTokens/full"
      ({ textDocument := doc } : SemanticTokensParams) SemanticTokens
    let ranged ← ask 3 "textDocument/semanticTokens/range"
      ({ textDocument := doc, range := ⟨⟨6, 0⟩, ⟨7, 0⟩⟩ } : SemanticTokensRangeParams) SemanticTokens
    let allTokens := decode text full
    let line := allTokens.filter (·.2.2 == 6)
    unless line == decode text ranged && line.map (·.1) ==
        #["atomStyle", "p", "BDD", "some", "q", "BDD", "q", "in", "p", ".", "lo",
          "&&", "q", "in", "p", ".", "hi", "fillStyle"] do
      throw <| IO.userError s!"unexpected tokens on selector: {repr line}"
    for token in #[("p", "variable", 6), ("BDD", "type", 6), ("lo", "property", 6),
        ("&&", "operator", 6), ("univ", "keyword", 9), ("«univ»", "property", 9),
        ("lean", "property", 9), ("fun", "keyword", 10), ("n", "variable", 10),
        ("+", "operator", 10), ("BDD", "type", 10), ("fls", "enumMember", 11)] do
      unless allTokens.contains token do throw <| IO.userError s!"missing {repr token}"
    let boundary := allTokens.filter (fun (_, kind, line) => kind == "macro" && line == 10)
    unless boundary.map (·.1) == #["lean", "(", ")"] do
      throw <| IO.userError s!"unexpected embedded Lean delimiters: {repr boundary}"
    let colors ← ask 4 "textDocument/documentColor" ({ textDocument := doc } : DocumentColorParams)
      (Array ColorInformation)
    let actual := colors.map fun c =>
      let rgba := [c.color.red, c.color.green, c.color.blue, c.color.alpha].map fun f =>
        (f * 255).round.toUInt32.toNat
      (slice text c.range, rgba)
    let expected := #[("\"#ffe082\"", [255, 224, 130, 255]), ("\"#abc\"", [170, 187, 204, 255]),
      ("\"#0F08\"", [0, 255, 0, 136]), ("\"#10203040\"", [16, 32, 48, 64]),
      ("\"#FFFFFF\"", [255, 255, 255, 255]), ("\"#321\"", [51, 34, 17, 255])]
    unless actual == expected do throw <| IO.userError s!"unexpected swatches: {repr actual}"
    let edited := source.replace "#ffe082" "red"
    Ipc.writeNotification ⟨"textDocument/didChange",
      { textDocument := { uri, version? := some 2 },
        contentChanges := #[.fullChange edited] : DidChangeTextDocumentParams }⟩
    sync 5 uri 2
    let colors ← ask 6 "textDocument/documentColor" ({ textDocument := doc } : DocumentColorParams)
      (Array ColorInformation)
    unless colors.size == 5 && colors.all (·.range.start.line != 6) do
      throw <| IO.userError "stale swatch after edit"
    Ipc.shutdown 7

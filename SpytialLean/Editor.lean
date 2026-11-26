module

public meta import Lean.Elab.InfoTree
public meta import Lean.Server.FileWorker.RequestHandling

namespace SpytialLean.Editor

open Lean Elab Lsp Server Server.FileWorker

meta section

private inductive Annotation where
  | token (kind : SemanticTokenType)
  | color (value : Lsp.Color)
  deriving TypeName

private def annotate (stx : Syntax) (annotation : Annotation) : TermElabM Unit := do
  if stx.getHeadInfo matches .original .. then
    pushInfoLeaf <| .ofCustomInfo { stx, value := .mk annotation }

public def highlight (stx : Syntax) (kind : SemanticTokenType) : TermElabM Unit :=
  annotate stx (.token kind)

private def hexColor? (s : String) : Option Lsp.Color := do
  let digits ← s.dropPrefix? "#"
  let digits := digits.toString
  guard <| [3, 4, 6, 8].contains digits.length && digits.toList.all Char.isHexDigit
  let width := if digits.length ≤ 4 then 1 else 2
  let channel (offset : Nat) : Option Float := do
    let part := (digits.drop (offset * width)).take width
    let value ← Syntax.decodeNatLitVal? ("0x" ++ part.toString)
    return Float.ofNat value / (if width == 1 then 15 else 255)
  let alpha ← if digits.length == 4 * width then channel 3 else pure 1
  return ⟨← channel 0, ← channel 1, ← channel 2, alpha⟩

public def colorLiteral (stx : Syntax) (s : String) : TermElabM Unit := do
  if let some color := hexColor? s then annotate stx (.color color)

private def collect (snaps : List Snapshots.Snapshot) (text : FileMap) (within : Lsp.Range)
    (pick : Lsp.Range → Annotation → Option α) : RequestM (Array α) := do
  let start := text.lspPosToUtf8Pos within.start
  let stop := text.lspPosToUtf8Pos within.end
  let mut found := #[]
  for snap in snaps do
    if snap.endPos <= start then continue
    RequestM.checkCancelled
    found := snap.infoTree.foldInfo (init := found) fun _ info acc => Id.run do
      let .ofCustomInfo custom := info | return acc
      let some mark := custom.value.get? Annotation | return acc
      let some range := text.lspRangeOfStx? custom.stx | return acc
      if range.start < within.start || within.end < range.end then return acc
      let some item := pick range mark | return acc
      return acc.push item
    if snap.endPos >= stop then break
  return found

private structure Token where
  range : Lsp.Range
  kind : Nat
  modifiers : Nat := 0
  deriving Inhabited

private structure TokenWriter where
  data : Array Nat := #[]
  prev : Lsp.Range := default

private def TokenWriter.emit (w : TokenWriter) (t : Token) : TokenWriter := Id.run do
  if t.range.start < w.prev.end then return w
  let p := t.range.start
  let delta := p.line - w.prev.start.line
  let col := if delta == 0 then p.character - w.prev.start.character else p.character
  return { data := w.data.push delta |>.push col |>.push (t.range.end.character - p.character)
             |>.push t.kind |>.push t.modifiers, prev := t.range }

/-- Merge in source order. An exact match refines the previous classification and keeps its
    modifiers. Other overlaps keep the original provider's token. -/
private def mergeTokens (base : SemanticTokens) (extra : Array Token) : SemanticTokens := Id.run do
  if extra.isEmpty then return base
  let mut pending := (extra.qsort (·.range.start < ·.range.start)).toList
  let mut w : TokenWriter := {}
  let mut pos : Lsp.Position := ⟨0, 0⟩
  let d := base.data
  for i in [0:d.size:5] do
    let line := pos.line + d[i]!
    let col := (if d[i]! == 0 then pos.character else 0) + d[i+1]!
    pos := ⟨line, col⟩
    let range : Lsp.Range := ⟨pos, ⟨line, col + d[i+2]!⟩⟩
    let mut kind := d[i+3]!
    while let t :: rest := pending do
      if pos < t.range.start then break
      if t.range == range then kind := t.kind
      else if t.range.end <= pos then w := w.emit t
      pending := rest
    w := w.emit ⟨range, kind, d[i+4]!⟩
  return { base with data := (pending.foldl TokenWriter.emit w).data }

private def wholeDocument (text : FileMap) : Lsp.Range :=
  ⟨⟨0, 0⟩, text.utf8PosToLspPos text.source.rawEndPos⟩

private def addTokens (base : SemanticTokens) (within : Option Lsp.Range) :
    RequestM SemanticTokens := do
  let doc ← RequestM.readDoc
  -- The original range handler already waited for its region. A full-file request
  -- streams the finished prefix and Lean schedules refreshes while elaboration continues.
  let (snaps, _, _) ← doc.cmdSnaps.getFinishedPrefix
  let text := doc.meta.text
  let tokens ← collect snaps text (within.getD (wholeDocument text)) fun range mark => do
    let .token kind := mark | none
    guard (range.start.line == range.end.line && range.start.character < range.end.character)
    return { range, kind := kind.toNat : Token }
  return mergeTokens base tokens

initialize
  chainLspRequestHandler "textDocument/semanticTokens/range"
    SemanticTokensRangeParams SemanticTokens fun p previous =>
      RequestM.mapRequestTaskCostly previous (addTokens · p.range)
  chainStatefulLspRequestHandler "textDocument/semanticTokens/full"
    SemanticTokensParams SemanticTokens SemanticTokensState (fun _ previous state => do
      return ({ previous with response := ← addTokens previous.response none }, state))
    fun _ => pure ()
  chainLspRequestHandler "textDocument/documentColor"
    DocumentColorParams (Array ColorInformation) fun _ previous => do
      let doc ← RequestM.readDoc
      RequestM.bindRequestTaskCheap previous fun base =>
        RequestM.mapTaskCostly doc.cmdSnaps.waitAll fun (snaps, _) => do
          let text := doc.meta.text
          let colors ← collect snaps text (wholeDocument text) fun range mark => do
            let .color color := mark | none
            return { range, color : ColorInformation }
          -- A tactic can elaborate the same written op on more than one goal.
          return (base ++ colors).toList.eraseDupsBy (·.range == ·.range) |>.toArray

end

end SpytialLean.Editor

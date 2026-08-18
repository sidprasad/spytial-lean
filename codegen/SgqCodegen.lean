/-
Generates `SpytialLean/SelectorGenerated.lean` from simple-graph-query's
language manifest.

    lake exe sgqCodegen           # regenerate (also: just gen-sgq)
    lake exe sgqCodegen --check   # fail if the checked-in file is stale (CI)

`Sel.toSGQ` writes the concrete syntax that spytial-core's evaluator reads, so
it has to know that engine's lexer and grammar: which names can be written
bare, how to escape the ones that cannot, how each operator is spelled, and
where each sits in the precedence cascade. All of that used to be a hand copy
of ForgeLexer.g4 and Forge.g4 sitting in Selector.lean, and it had already gone
stale -- the reserved-word list still carried the temporal keywords that
simple-graph-query removed from the grammar.

simple-graph-query publishes `docs/sgq-language.json` instead. This program
turns it into the tables `Selector.lean` lowers through.

The generator refuses to emit output it cannot account for: an operator the
preference table below does not resolve, a fixity it has no shape for, or a
manifest field missing outright is an error naming the construct. An sgq
release that grows the language stops codegen by name rather than silently
lowering to syntax the engine no longer accepts.
-/
import Lean.Data.Json

open Lean (Json)

def manifestPath : System.FilePath :=
  "node_modules" / "simple-graph-query" / "docs" / "sgq-language.json"

def outputPath : System.FilePath := "SpytialLean" / "SelectorGenerated.lean"

def die {α} (msg : String) : IO α := throw (IO.userError s!"sgq-codegen: {msg}")

def unwrap {α} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => die s!"{ctx}: {e}"

/-! ## JSON access -/

def jObj (ctx : String) (j : Json) (k : String) : IO Json :=
  unwrap s!"{ctx}.{k}" (j.getObjVal? k)

def jStr (ctx : String) (j : Json) (k : String) : IO String := do
  unwrap s!"{ctx}.{k}" (← jObj ctx j k).getStr?

def jNat (ctx : String) (j : Json) (k : String) : IO Nat := do
  unwrap s!"{ctx}.{k}" (← jObj ctx j k).getNat?

def jArr (ctx : String) (j : Json) (k : String) : IO (Array Json) := do
  unwrap s!"{ctx}.{k}" (← jObj ctx j k).getArr?

def jStrArr (ctx : String) (j : Json) (k : String) : IO (Array String) := do
  (← jArr ctx j k).mapM fun v => unwrap s!"{ctx}.{k}[]" v.getStr?

/-- A manifest string that must be exactly one character. -/
def jChar (ctx : String) (j : Json) (k : String) : IO Char := do
  let s ← jStr ctx j k
  match s.toList with
  | [c] => pure c
  | _ => die s!"{ctx}.{k}: expected a single character, got {s.quote}"

/-! ## Which spelling spytial-lean writes

A token can have aliases (`or` is also `||`). The manifest lists them in
grammar order and takes no view; which one to *emit* is this package's house
style, so it is stated here rather than guessed. Every operator or part with
more than one spelling needs an entry: a new alias upstream is then a codegen
error, not a silent change of what we emit. -/

/-- Roles whose several spellings are alternatives to choose between at each use
    (an arrow's multiplicity), not aliases for one thing. These emit as a list;
    everything else has to resolve to the one spelling we write. -/
def alternativeRoles : List String := ["product.multiplicity"]

def preferredSpelling : List (String × String) :=
  [ ("or", "or"), ("and", "and"), ("not", "not"), ("iff", "iff"),
    ("implies", "implies"), ("atMost", "<="),
    -- `!in` / `!ni` / `!=` read better than the `not` prefix, and are what the
    -- selector reference documents.
    ("comparison.negation", "!") ]

def pick (what : String) (spellings : Array String) : IO String := do
  match preferredSpelling.lookup what with
  | some s =>
    unless spellings.contains s do
      die s!"{what}: preferred spelling {s.quote} is no longer one of {spellings}"
    return s
  | none =>
    match spellings.toList with
    | [s] => return s
    | _ => die s!"{what} has several spellings {spellings} and no entry in preferredSpelling"

/-! ## Lean literals -/

def leanStr (s : String) : String :=
  "\"" ++ s.foldl (init := "") (fun acc c =>
    acc ++ (match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
      | c => if c.val < 0x20 then s!"\\x{String.ofList (Nat.toDigits 16 c.toNat)}" else c.toString)) ++ "\""

def leanChar (c : Char) : String :=
  match c with
  | '\'' => "'\\''" | '\\' => "'\\\\'" | '\n' => "'\\n'" | '\t' => "'\\t'" | '\r' => "'\\r'"
  | c => if c.val < 0x20 then s!"Char.ofNat {c.toNat}" else s!"'{c}'"

def leanStrList (xs : Array String) : String :=
  "[" ++ String.intercalate ", " (xs.map leanStr).toList ++ "]"

def leanNatList (xs : Array Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString).toList ++ "]"

/-- A `Char -> Bool` test for a manifest character class. -/
def charClassBody (ctx : String) (j : Json) : IO String := do
  let ranges ← (← jArr ctx j "ranges").mapM fun r => do
    let pair ← unwrap s!"{ctx}.ranges[]" r.getArr?
    match pair.toList with
    | [lo, hi] => do
      let lo ← unwrap ctx lo.getStr?
      let hi ← unwrap ctx hi.getStr?
      match lo.toList, hi.toList with
      | [lo], [hi] => return s!"({leanChar lo} ≤ c && c ≤ {leanChar hi})"
      | _, _ => die s!"{ctx}.ranges: bounds must be single characters"
    | _ => die s!"{ctx}.ranges: expected [lo, hi]"
  let chars ← (← jStrArr ctx j "chars").mapM fun s =>
    match s.toList with
    | [c] => pure s!"c == {leanChar c}"
    | _ => die s!"{ctx}.chars: expected single characters"
  let clauses := ranges ++ chars
  if clauses.isEmpty then die s!"{ctx}: empty character class"
  return String.intercalate " || " clauses.toList

/-! ## Emit -/

structure Operator where
  id : String
  construct : String
  text : String
  prec : Nat
  operands : Array Nat

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let txt ← try IO.FS.readFile manifestPath catch _ =>
    die s!"manifest not found at {manifestPath} — run `pnpm install` first (any `lake build` does)"
  let manifest ← unwrap "manifest" (Json.parse txt)
  let version ← jStr "manifest" manifest "sgqVersion"

  let identifier ← jObj "manifest" manifest "identifier"
  let bare ← jObj "identifier" identifier "bare"
  let headTest ← charClassBody "identifier.bare.head" (← jObj "bare" bare "head")
  let restTest ← charClassBody "identifier.bare.rest" (← jObj "bare" bare "rest")
  let bareMin ← jNat "bare" bare "minLength"
  let reserved ← jStrArr "identifier" identifier "reserved"

  let quoted ← jObj "identifier" identifier "quoted"
  let quotedDelim ← jChar "quoted" quoted "delimiter"
  let quotedEsc ← jChar "quoted" quoted "escape"
  let quotedMust ← jStrArr "quoted" quoted "mustEscape"
  let quotedMin ← jNat "quoted" quoted "minLength"
  unless (← jObj "quoted" quoted "escapeDecodes").getObjVal? "n" |>.toOption.isNone do
    die "identifier.quoted now decodes escapes; Selector.lean assumes a backslash only removes itself"

  let str ← jObj "manifest" manifest "string"
  let strDelim ← jChar "string" str "delimiter"
  let strEsc ← jChar "string" str "escape"
  let strMust ← jStrArr "string" str "mustEscape"
  let strDecodes ← unwrap "string.escapeDecodes" (← jObj "string" str "escapeDecodes").getObj?

  let builtins ← jObj "manifest" manifest "builtins"
  let binaryB ← jStrArr "builtins" builtins "binary"
  let unaryB ← jStrArr "builtins" builtins "unary"
  let setB ← jStrArr "builtins" builtins "set"

  -- Operators, flattened out of the cascade. Ids are unique across the table,
  -- so they name the generated defs directly.
  let constructs ← jArr "manifest" manifest "constructs"
  let mut ops : Array Operator := #[]
  let mut parts : Array (String × String × String) := #[]
  let mut alternatives : Array (String × String × Array String) := #[]
  for c in constructs do
    let cid ← jStr "construct" c "id"
    let prec ← jNat cid c "precedence"
    let operands ← (← jArr cid c "operands").mapM fun v => unwrap s!"{cid}.operands[]" v.getNat?
    for o in ← jArr cid c "operators" do
      let oid ← jStr s!"{cid}.operators[]" o "id"
      let spellings ← jStrArr s!"{cid}.{oid}" o "spellings"
      ops := ops.push { id := oid, construct := cid, text := ← pick oid spellings, prec, operands }
    for (role, raw) in (← unwrap s!"{cid}.parts" (← jObj cid c "parts").getObj?).toArray do
      let spellings ← (← unwrap s!"{cid}.parts.{role}" raw.getArr?).mapM fun v =>
        unwrap s!"{cid}.parts.{role}[]" v.getStr?
      if alternativeRoles.contains s!"{cid}.{role}" then
        alternatives := alternatives.push (cid, role, spellings)
      else
        parts := parts.push (cid, role, ← pick s!"{cid}.{role}" spellings)

  let dup := ops.filter fun o => 1 < (ops.filter (·.id == o.id)).size
  unless dup.isEmpty do die s!"operator ids are not unique: {dup.map (·.id)}"

  let mut L : Array String := #[]
  L := L ++ #[
    "/-",
    s!"GENERATED by `lake exe sgqCodegen` (just gen-sgq) from simple-graph-query",
    s!"{version}'s docs/sgq-language.json. Do not edit; edit the generator instead.",
    "",
    "These are the engine's own lexical and grammatical facts, not this package's",
    "choices: what a bare name may contain, what has to be quoted, how each",
    "operator is spelled, and where each sits in the precedence cascade.",
    "-/",
    "module",
    "",
    "namespace SpytialLean.Sgq",
    "",
    "/-- Where a construct sits in the cascade, and the level each of its operand",
    "    slots descends to. A subexpression needs parentheses exactly when its own",
    "    `prec` is below the level of the slot it fills -- which is not always the",
    "    neighbouring level, so these are read rather than assumed. -/",
    "public meta structure Op where",
    "  text : String",
    "  prec : Nat",
    "  operands : List Nat",
    "  deriving Repr, Inhabited",
    "",
    "/-- The level of the loosest expression: what a delimiter accepts inside it. -/",
    "public meta def loosest : Nat := 0",
    ""
  ]

  L := L.push "/-! ## Operators -/"
  L := L.push ""
  -- Ids come from another language's vocabulary, so some of them (`let`,
  -- `universe`, `this`) are Lean keywords. Defining every one guillemeted is
  -- uniform and needs no list of which those are; uses read plainly except for
  -- the handful that Lean also wants escaped.
  for o in ops do
    L := L.push s!"/-- `{o.text}` — {o.id}, from the {o.construct} construct. -/"
    L := L.push s!"public meta def «{o.id}» : Op :="
    L := L.push s!"  \{ text := {leanStr o.text}, prec := {o.prec}, operands := {leanNatList o.operands} }"
  L := L.push ""

  L := L.push "/-! ## Fixed syntax -/"
  L := L.push ""
  for (cid, role, text) in parts do
    L := L.push s!"/-- The {role} of a {cid}. -/"
    L := L.push s!"public meta def «{cid}».«{role}» : String := {leanStr text}"
  for (cid, role, spellings) in alternatives do
    L := L.push s!"/-- The {role} spellings a {cid} chooses between. -/"
    L := L.push s!"public meta def «{cid}».«{role}» : List String := {leanStrList spellings}"
  L := L.push ""

  L := L ++ #[
    "/-! ## Names -/",
    "",
    "/-- Spellings a bare identifier cannot carry: they lex as some other token. -/",
    s!"public meta def reserved : List String :=",
    s!"  {leanStrList reserved}",
    "",
    "public meta def bareHead (c : Char) : Bool := " ++ headTest,
    "",
    "public meta def bareRest (c : Char) : Bool := " ++ restTest,
    "",
    s!"public meta def bareMinLength : Nat := {bareMin}",
    "",
    s!"public meta def quoteDelimiter : Char := {leanChar quotedDelim}",
    s!"public meta def quoteEscape : Char := {leanChar quotedEsc}",
    "/-- Characters the quoted form refuses raw, so an encoder must escape them. -/",
    s!"public meta def quoteMustEscape : List Char := [{String.intercalate ", " (quotedMust.toList.map fun s => leanChar s.toList.head!)}]",
    "/-- The shortest name the quoted form can spell; the empty name has no spelling at all. -/",
    s!"public meta def quoteMinLength : Nat := {quotedMin}",
    "",
    "/-! ## String literals -/",
    "",
    s!"public meta def stringDelimiter : Char := {leanChar strDelim}",
    s!"public meta def stringEscape : Char := {leanChar strEsc}",
    s!"public meta def stringMustEscape : List Char := [{String.intercalate ", " (strMust.toList.map fun s => leanChar s.toList.head!)}]"
  ]
  L := L.push ""
  L := L.push "/-- Readable spellings for characters that would otherwise ride raw. The"
  L := L.push "    engine resolves these; anything else after the escape denotes itself. -/"
  L := L.push "public meta def stringEscapeSpelling : Char → Option Char"
  for (spelling, decoded) in strDecodes.toArray do
    let decoded ← unwrap "string.escapeDecodes[]" decoded.getStr?
    match spelling.toList, decoded.toList with
    -- `Option.some` in full: `some` is also an sgq operator, so the generated
    -- defs above shadow the constructor inside this namespace.
    | [s], [d] => L := L.push s!"  | {leanChar d} => Option.some {leanChar s}"
    | _, _ => die "string.escapeDecodes: expected single characters"
  L := L.push "  | _ => none"
  L := L.push ""

  L := L ++ #[
    "/-! ## Builtins -/",
    "",
    s!"public meta def binaryBuiltins : List String := {leanStrList binaryB}",
    s!"public meta def unaryBuiltins : List String := {leanStrList unaryB}",
    "/-- Aggregators: they fold a set to a number. -/",
    s!"public meta def setBuiltins : List String := {leanStrList setB}",
    "",
    "end SpytialLean.Sgq"
  ]

  let out := String.intercalate "\n" L.toList ++ "\n"

  if check then
    let existing ← try IO.FS.readFile outputPath catch _ => pure ""
    if existing == out then
      IO.println s!"{outputPath} is up to date (simple-graph-query {version})."
      return 0
    IO.eprintln s!"{outputPath} is stale — run `just gen-sgq` and commit the diff."
    return 1
  IO.FS.writeFile outputPath out
  IO.println s!"wrote {outputPath} (simple-graph-query {version})."
  return 0

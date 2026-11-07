import Harness.Common

namespace Harness.Audit
open Harness

/-- Mask comments and quoted literals while retaining line/column positions. -/
def mask (source : String) : Except String String := Id.run do
  let chars := source.toList.toArray
  let mut result := #[]
  let mut i := 0
  let mut depth := 0
  let mut quoted := false
  while i < chars.size do
    let c := chars[i]!
    let next := chars[i+1]?.getD '\x00'
    if depth > 0 then
      if c == '/' && next == '-' then
        depth := depth + 1; result := result ++ #[' ', ' ']; i := i + 2
      else if c == '-' && next == '/' then
        depth := depth - 1; result := result ++ #[' ', ' ']; i := i + 2
      else
        result := result.push (if c == '\n' then c else ' '); i := i + 1
    else if quoted then
      if c == '\\' then result := result ++ #[' ', ' ']; i := i + 2
      else
        quoted := c != '"'; result := result.push (if c == '\n' then c else ' '); i := i + 1
    else if c == '/' && next == '-' then
      depth := 1; result := result ++ #[' ', ' ']; i := i + 2
    else if c == '-' && next == '-' then
      while i < chars.size && chars[i]! != '\n' do
        result := result.push ' '; i := i + 1
    else if c == '"' then
      quoted := true; result := result.push ' '; i := i + 1
    else if c == '\'' then
      let length := if next == '\\' then
          if chars[i+2]? == some 'u' then 8 else if chars[i+2]? == some 'x' then 6 else 4
        else 3
      let valid := chars[i+length-1]? == some '\'' && next != '\n' && next != '\'' &&
        (next != '\\' || (length == 4 || ((chars.toList.drop (i+3)).take (length-4)).all Char.isHexDigit))
      if valid then
        result := result ++ Array.replicate length ' '; i := i + length
      else result := result.push c; i := i + 1
    else result := result.push c; i := i + 1
  if depth != 0 || quoted then return .error "unterminated comment or string"
  return .ok (String.ofList result.toList)

def identifierChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''
def tokens (code : String) : List String :=
  words (String.ofList (code.toList.map (fun c => if identifierChar c then c else ' ')))
def plainName (name : String) : Bool :=
  !name.isEmpty && (name.toList.head!.isAlpha || name.startsWith "_") &&
    name.toList.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))

def discover (source : String) : Except String (List String) := do
  let code ← mask source
  let ts := tokens code
  let spaces := (lines code).filter (·.startsWith "namespace ")
  unless spaces.length == 1 && (ts.filter (· == "namespace")).length == 1 do
    throw "requires one explicit namespace"
  let namespaceWords := words spaces.head!
  unless namespaceWords.length == 2 && (namespaceWords[1]!.splitOn ".").all plainName do
    throw "unsupported namespace"
  if ts.contains "private" then throw "private declarations are outside audited style"
  let mut names := []
  for line in lines code do
    if line.startsWith "theorem " then
      let suffix := (line.drop 8).toString
      let name := String.ofList (suffix.toList.takeWhile (fun c => !c.isWhitespace && c != '(' && c != '{' && c != ':'))
      unless plainName name do throw "unsupported theorem name"
      names := names ++ [namespaceWords[1]! ++ "." ++ name]
  unless names.length == (ts.filter (fun t => t == "theorem" || t == "lemma")).length do
    throw "unsupported theorem header; use column-zero public theorem NAME"
  unless names.eraseDups.length == names.length do throw "duplicate theorem names"
  return names

def allowed := ["propext", "Classical.choice", "Quot.sound"]

def reportLines (output : String) : Except String (List String) := do
  let mut result := []
  let mut pending := ""
  for line in lines output do
    if !pending.isEmpty then
      if line.startsWith "'" then throw "Unterminated audit report"
      pending := pending ++ " " ++ trim line
      if pending.endsWith "]" then
        result := result ++ [pending]; pending := ""
    else if line.startsWith "'" then
      if contains line " depends on axioms: [" && !line.endsWith "]" then pending := line
      else result := result ++ [line]
  unless pending.isEmpty do throw "Unterminated audit report"
  return result

def reports (output : String) : Except String (List (String × List String)) := do
  let mut result := []
  for line in ← reportLines output do
    if line.startsWith "'" then
      let parts := line.splitOn "'"
      unless parts.length == 3 do throw s!"Malformed audit report: {line}"
      let name := parts[1]!
      let suffix := parts[2]!
      if suffix == " does not depend on any axioms" then result := result ++ [(name, [])]
      else if suffix.startsWith " depends on axioms: [" && suffix.endsWith "]" then
        let deps := (((suffix.drop 21).toString.dropEnd 1).toString.splitOn ",").map trim |>.filter (! ·.isEmpty)
        unless deps.all allowed.contains do throw s!"Unexpected proof dependencies for {name}: {deps}"
        result := result ++ [(name, deps)]
      else throw s!"Malformed audit report: {line}"
  return result

def verifyReports (expected : List String) (output : String) : IO Unit := do
  let actual ← IO.ofExcept (reports output)
  ensure (!expected.isEmpty && (actual.map Prod.fst).mergeSort (· ≤ ·) == expected.mergeSort (· ≤ ·))
    "Proof audit did not report exactly every requested declaration"

def sourceGuard (source : String) : Bool :=
  let ts := words (String.ofList (source.toList.map (fun c => if c.isAlphanum || c == '_' then c else ' ')))
  let compact := String.ofList (source.toList.filter (! ·.isWhitespace))
  !(["sorry", "admit", "unsafe", "axiom", "native_decide", "extern", "implemented_by"].any ts.contains) &&
    !(contains compact "debug.skipKernelTC") && !(contains compact "decide+native") &&
    !(contains compact "@[extern") && !(contains compact "@[implemented_by")

def selfTest : IO Unit := do
  for source in [
    "namespace N\n/- theorem hidden /- nested -/ -/\n@[simp]\ntheorem visible : True := by trivial\nend N",
    "namespace N\ndef quote : Char := '\"'\ntheorem visible : True := by trivial\nend N",
    "namespace N\ndef slash : Char := '\\\\'\ntheorem visible : True := by trivial\nend N"] do
    ensure ((discover source).toOption == some ["N.visible"]) "Audit lexer lost a theorem"
  for declaration in ["private theorem hidden", "private\ntheorem hidden", "@[simp] theorem hidden",
      " theorem hidden", "theorem\nhidden", "theorem hidden'", "theorem hidden.extra"] do
    ensure (discover s!"namespace N\n{declaration} : True := by trivial\nend N" |>.toOption.isNone) "Audit accepted unsupported declaration"
  for output in ["'N.t' depends on axioms: [sorryAx]", "'N.t' bogus", "'N.t' depends on axioms: [propext,", "'N.t' depends on axioms: [propext,\n sorryAx]"] do
    ensure (reports output |>.toOption.isNone) "Audit accepted invalid dependencies"
  verifyReports ["N.t"] "'N.t' depends on axioms: [propext, Classical.choice, Quot.sound]"
  verifyReports ["N.t"] "'N.t' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
  for output in ["", "'N.t' does not depend on any axioms\n'N.t' does not depend on any axioms",
      "'N.other' does not depend on any axioms"] do
    let rejected ← try verifyReports ["N.t"] output; pure false catch _ => pure true
    ensure rejected "Audit accepted missing/duplicate/wrong report"
  for source in ["sorry", "admit", "unsafe", "axiom", "native_decide", "debug.skipKernelTC", "decide  +native", "@[extern x]", "@[implemented_by x]", "@[ extern x]", "decide+native", "@[inline, extern x]", "attribute [implemented_by other] f", "attribute [extern x] f"] do
    ensure (!sourceGuard source) s!"Source guard accepted {source}"
  check "audit discovery and policy self-tests" true

end Harness.Audit

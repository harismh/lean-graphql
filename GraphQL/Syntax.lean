import GraphQL.Schema

namespace GraphQL

inductive InputValue where
  | null | string (s : String) | int (i : Int) | boolean (b : Bool)
  | enumValue (s : String) | variable (name : String)
  | list (xs : List InputValue) | object (xs : List (String × InputValue))
  deriving Repr, BEq, Inhabited

inductive Presence (α : Type) where
  | missing | null | value (a : α)
  deriving Repr, BEq, Inhabited

structure Directive where
  name : String
  condition : InputValue
  deriving Repr, BEq, Inhabited

inductive Selection where
  | field (name key : String) (args : List (String × InputValue))
      (directives : List Directive) (children : List Selection) (offset : Nat)
  | fragment (onType : String) (children : List Selection) (offset : Nat)
  deriving Repr, BEq, Inhabited

structure VariableDef where
  name : String
  type : TypeRef
  defaultValue : Option InputValue := none
  deriving Repr, BEq, Inhabited

structure Operation where
  name : Option String
  variables : List VariableDef
  selections : List Selection
  deriving Repr, BEq, Inhabited

namespace Syntax

inductive TokenKind where
  | name | punctuation | string | number
  deriving BEq, Repr

structure Token where
  text : String
  kind : TokenKind
  offset : Nat
  deriving Repr

def nameStart (c : Char) : Bool := c.isAlpha && c.toNat < 128 || c == '_'
def nameRest (c : Char) : Bool := nameStart c || c.isDigit

def quoted (fuel offset : Nat) (chars : List Char) (acc : List Char) : Except String (String × List Char × Nat) :=
  match fuel, chars with
  | 0, _ | _, [] => .error s!"unterminated string at character {offset}"
  | _ + 1, '"' :: rest =>
    let source := String.ofList (('"' :: acc).reverse)
    match Lean.Json.parse source with
    | .ok (.str value) => .ok (value, rest, offset + 1)
    | _ => .error s!"invalid string escape at character {offset}"
  | n + 1, '\\' :: c :: rest => quoted n (offset + 2) rest (c :: '\\' :: acc)
  | n + 1, '\t' :: rest => quoted n (offset + 1) rest ('t' :: '\\' :: acc)
  | n + 1, c :: rest => quoted n (offset + 1) rest (c :: acc)

def lexLoop (fuel offset : Nat) (chars : List Char) (acc : List Token) : Except String (List Token) :=
  match fuel, chars with
  | _, [] => .ok acc.reverse
  | 0, _ => .error "token budget exhausted"
  | n + 1, c :: rest =>
    if c.isWhitespace || c == ',' then lexLoop n (offset + 1) rest acc
    else if c == '#' then
      let skipped := rest.takeWhile (· != '\n')
      lexLoop n (offset + 1 + skipped.length) (rest.drop skipped.length) acc
    else if nameStart c then
      let tail := rest.takeWhile nameRest
      let word := String.ofList (c :: tail)
      lexLoop n (offset + 1 + tail.length) (rest.drop tail.length) (⟨word, .name, offset⟩ :: acc)
    else if c.isDigit || c == '-' then
      let tail := rest.takeWhile (·.isDigit)
      let word := String.ofList (c :: tail)
      let digits := if c == '-' then tail else c :: tail
      let remaining := rest.drop tail.length
      if digits.isEmpty || remaining.head?.any (fun ch => nameStart ch || ch == '.' || ch == '-') then
        .error s!"invalid integer literal at character {offset}"
      else if digits.length > 1 && digits.head? == some '0' then
        .error s!"integer literal has a leading zero at character {offset}"
      else lexLoop n (offset + 1 + tail.length) (rest.drop tail.length) (⟨word, .number, offset⟩ :: acc)
    else if c == '"' then do
      let (value, rest, next) ← quoted n (offset + 1) rest ['"']
      lexLoop n next rest (⟨value, .string, offset⟩ :: acc)
    else if "{}():![]=$@|&".contains c then
      lexLoop n (offset + 1) rest (⟨String.singleton c, .punctuation, offset⟩ :: acc)
    else if c == '.' && rest.take 2 == ['.', '.'] then
      lexLoop n (offset + 3) (rest.drop 2) (⟨"...", .punctuation, offset⟩ :: acc)
    else .error s!"unsupported character '{c}' at character {offset}"

def lex (source : String) : Except String (List Token) :=
  if source.length > 65536 then .error "document exceeds 65536 characters"
  else lexLoop (source.length + 1) 0 source.toList []

abbrev Parser := StateT (List Token) (Except String)

def peek (kind : TokenKind := .punctuation) : Parser String := do
  match (← get).head? with
  | none => return "<end>"
  | some t => return if t.kind == kind then t.text else "<other>"
def take : Parser Token := do
  match ← get with
  | [] => throw "unexpected end of document"
  | t :: rest => set rest; return t

def expect (text : String) : Parser Unit := do
  let token ← take
  let kind := if text.toList.head?.any nameStart then TokenKind.name else .punctuation
  unless token.kind == kind && token.text == text do
    throw s!"expected '{text}', found '{token.text}' at character {token.offset}"

def name : Parser String := do
  let token ← take
  unless token.kind == .name do throw s!"expected a name at character {token.offset}"
  return token.text

def typeRef : Nat → Parser TypeRef
  | 0 => throw "type reference nesting exceeds limit"
  | fuel + 1 => do
    let base ← if (← peek) == "[" then do
      expect "["
      let item ← typeRef fuel
      expect "]"
      pure (TypeRef.list item)
    else pure (TypeRef.named (← name))
    if (← peek) == "!" then expect "!"; return base.require
    else return base

def argumentDefs : Nat → Parser (List Argument)
  | 0 => throw "argument budget exhausted"
  | fuel + 1 => do
    if (← peek) == ")" then expect ")"; return []
    let n ← name
    expect ":"
    let t ← typeRef 32
    if (← peek) == "=" then throw "SDL argument defaults are not supported in this prototype"
    return ⟨n, t⟩ :: (← argumentDefs fuel)

def fields : Nat → Parser (List Field)
  | 0 => throw "field budget exhausted"
  | fuel + 1 => do
    if (← peek) == "}" then expect "}"; return []
    let n ← name
    let args ← if (← peek) == "(" then expect "("; argumentDefs fuel else pure []
    expect ":"
    let t ← typeRef 32
    return ⟨n, t, args⟩ :: (← fields fuel)

def enumMembers : Nat → Parser (List String)
  | 0 => throw "enum budget exhausted"
  | fuel + 1 => do
    if (← peek) == "}" then expect "}"; return []
    return (← name) :: (← enumMembers fuel)

def separatedNames (separator : String) : Nat → Parser (List String)
  | 0 => throw "member budget exhausted"
  | fuel + 1 => do
    let n ← name
    if (← peek) == separator then
      expect separator
      return n :: (← separatedNames separator fuel)
    else return [n]

def definitions : Nat → Parser (List TypeDef)
  | 0 => throw "schema budget exhausted"
  | fuel + 1 => do
    if (← peek) == "<end>" then return []
    let keyword ← name
    let n ← name
    let definition ← match keyword with
    | "scalar" => pure { name := n, kind := .scalar : TypeDef }
    | "enum" => do
      expect "{"
      pure { name := n, kind := .enumType, members := (← enumMembers fuel) }
    | "union" => do
      expect "="
      pure { name := n, kind := .union, members := (← separatedNames "|" fuel) }
    | "type" | "interface" | "input" => do
      let implements ← if (← peek .name) == "implements" then
        if keyword == "input" then throw "input objects cannot implement interfaces"
        expect "implements"; separatedNames "&" fuel else pure []
      expect "{"
      let fs ← fields fuel
      let kind := if keyword == "type" then Kind.object else if keyword == "input" then .input else .interface
      pure { name := n, kind, fields := fs, implements }
    | _ => throw s!"unsupported SDL definition '{keyword}'"
    return definition :: (← definitions fuel)

/-- Input nesting and list/object width are independent limits. -/
def inputValue : Nat → Parser InputValue
  | 0 => throw "input nesting exceeds 128 levels"
  | fuel + 1 => do
    let t ← take
    if t.kind == .string then return .string t.text
    if t.kind == .number then
      match t.text.toInt? with
      | some i => return .int i
      | none => throw s!"invalid integer at character {t.offset}"
    match t.text with
    | "null" => return .null
    | "true" => return .boolean true
    | "false" => return .boolean false
    | "$" => return .variable (← name)
    | "[" =>
      let mut items := #[]
      for _ in [:4097] do
        if (← peek) == "]" then expect "]"; return .list items.toList
        if items.size == 4096 then throw "input list exceeds 4096 items"
        items := items.push (← inputValue fuel)
      throw "input item limit exceeded"
    | "{" =>
      let mut fields := #[]
      for _ in [:4097] do
        if (← peek) == "}" then expect "}"; return .object fields.toList
        if fields.size == 4096 then throw "input object exceeds 4096 fields"
        let n ← name
        expect ":"
        fields := fields.push (n, ← inputValue fuel)
      throw "input field limit exceeded"
    | n =>
      if t.kind == .name then pure (.enumValue n)
      else throw s!"expected input value at character {t.offset}"

def arguments : Nat → Parser (List (String × InputValue))
  | 0 => throw "argument budget exhausted"
  | fuel + 1 => do
    if (← peek) == ")" then expect ")"; return []
    let n ← name
    expect ":"
    return (n, ← inputValue 128) :: (← arguments fuel)

def directives : Nat → Parser (List Directive)
  | 0 => throw "directive budget exhausted"
  | fuel + 1 => do
    if (← peek) != "@" then return []
    expect "@"
    let n ← name
    unless n == "skip" || n == "include" do throw s!"unsupported directive @{n}"
    expect "("
    expect "if"
    expect ":"
    let condition ← inputValue 8
    expect ")"
    return ⟨n, condition⟩ :: (← directives fuel)

/-- Depth does not depend on sibling count. Overall work is bounded in validation. -/
def selections : Nat → Parser (List Selection)
  | 0 => throw "selection nesting exceeds 64 levels"
  | fuel + 1 => do
    let mut result := #[]
    for _ in [:4097] do
      if (← peek) == "}" then expect "}"; return result.toList
      if result.size == 4096 then throw "selection set exceeds 4096 entries"
      let offset := (← get).head?.map (·.offset) |>.getD 0
      let selection ← if (← peek) == "..." then do
        expect "..."
        expect "on"
        let target ← name
        expect "{"
        let children ← selections fuel
        if children.isEmpty then throw "empty fragment selection"
        pure (.fragment target children offset)
      else do
        let first ← name
        let (n, key) ← if (← peek) == ":" then expect ":"; pure ((← name), first)
          else pure (first, first)
        let args ← if (← peek) == "(" then expect "("; arguments 4096 else pure []
        let ds ← directives 8
        let children ← if (← peek) == "{" then do
          expect "{"
          let xs ← selections fuel
          if xs.isEmpty then throw "empty field selection"
          pure xs
        else pure []
        pure (.field n key args ds children offset)
      result := result.push selection
    throw "selection count limit exceeded"

def variableDefs : Nat → Parser (List VariableDef)
  | 0 => throw "variable budget exhausted"
  | fuel + 1 => do
    if (← peek) == ")" then expect ")"; return []
    expect "$"
    let n ← name
    expect ":"
    let t ← typeRef 32
    let defaultValue ← if (← peek) == "=" then expect "="; pure (some (← inputValue 128)) else pure none
    return ⟨n, t, defaultValue⟩ :: (← variableDefs fuel)

def operation (budget : Nat) : Parser Operation := do
  let (n, vs) ← if (← peek) == "{" then pure (none, []) else do
    expect "query"
    let n ← if (← peek) == "(" || (← peek) == "{" then pure none else pure (some (← name))
    let vs ← if (← peek) == "(" then expect "("; variableDefs budget else pure []
    pure (n, vs)
  expect "{"
  let sels ← selections 64
  if sels.isEmpty then throw "empty operation selection"
  return ⟨n, vs, sels⟩

def run (p : Parser α) (tokens : List Token) : Except String α := do
  let (value, rest) ← p.run tokens
  match rest with
  | [] => return value
  | t :: _ => throw s!"unexpected '{t.text}' at character {t.offset}; only one operation is supported"

end Syntax

def parseSchema (source : String) : Except String Schema := do
  let tokens ← Syntax.lex source
  return ⟨← Syntax.run (Syntax.definitions (tokens.length + 1)) tokens, "Query"⟩

def parseOperation (source : String) : Except String Operation := do
  let tokens ← Syntax.lex source
  Syntax.run (Syntax.operation (min 4096 (tokens.length + 1))) tokens

end GraphQL

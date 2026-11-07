import GraphQL.Value

namespace GraphQL.HttpJson

private def checkNumber (chars : List Char) : Except String Unit := do
  if chars.isEmpty then return ()
  if chars.length > 128 then throw "JSON number exceeds 128 characters"
  let text := (String.ofList chars.reverse).toLower
  match text.splitOn "e" with
  | [_, exponent] =>
    let exponent := if exponent.startsWith "+" then (exponent.drop 1).toString else exponent
    let some n := exponent.toInt? | throw "invalid JSON exponent"
    if n.natAbs > 308 then throw "JSON exponent exceeds prototype limit"
  | _ => return ()

/-- Bound nesting before calling Lean's JSON parser; reject duplicate decoded keys.
    This scanner is tested, not formally verified. -/
def checkEnvelope (body : String) : Except String Unit := do
  if body.utf8ByteSize > 65536 then throw "request body exceeds 65536 bytes"
  let mut stack : List (Bool × List String) := []
  let mut quoted := false
  let mut escaped := false
  let mut chars : List Char := []
  let mut lastString : Option String := none
  let mut number : List Char := []
  for c in body.toList do
    if quoted then
      if escaped then
        chars := c :: chars
        escaped := false
      else if c == '\\' then
        chars := c :: chars
        escaped := true
      else if c == '"' then
        let source := "\"" ++ String.ofList chars.reverse ++ "\""
        let .ok (.str value) := Lean.Json.parse source | throw "invalid JSON string"
        lastString := some value
        quoted := false
      else chars := c :: chars
    else
      if c.isDigit || c == '-' || (!number.isEmpty && "+.eE".contains c) then
        number := c :: number
        if number.length > 128 then throw "JSON number exceeds 128 characters"
      else
        checkNumber number
        number := []
      if c == '"' then
        quoted := true
        chars := []
      else if c == '{' || c == '[' then
        stack := (c == '{', []) :: stack
        if stack.length > 32 then throw "JSON nesting exceeds 32 levels"
      else if c == '}' || c == ']' then
        stack := stack.drop 1
      else if c == ':' then
        match stack, lastString with
        | (true, keys) :: tail, some key =>
          if keys.contains key then throw s!"duplicate JSON key '{key}'"
          stack := (true, key :: keys) :: tail
          lastString := none
        | _, _ => pure ()
  checkNumber number
  if quoted then throw "unterminated JSON string"

def toInput : Nat → Lean.Json → Except String InputValue
  | 0, _ => throw "JSON nesting exceeds limit"
  | _ + 1, .null => return .null
  | _ + 1, .str s => return .string s
  | _ + 1, .bool b => return .boolean b
  | _ + 1, .num n => do
    if n.exponent > 308 then throw "JSON exponent exceeds prototype limit"
    let denominator : Int := Int.ofNat (10 ^ n.exponent)
    if n.mantissa % denominator != 0 then throw "non-integral JSON numbers are unsupported in this prototype"
    return .int (n.mantissa / denominator)
  | fuel + 1, .arr xs => return .list (← xs.toList.mapM (toInput fuel))
  | fuel + 1, .obj fields => return .object (← fields.toList.mapM fun (k, v) => return (k, ← toInput fuel v))

structure Envelope where
  query : String
  operationName : Option String
  variables : List (String × InputValue)

def decode (json : Lean.Json) : Except String Envelope := do
  let fields ← json.getObj?
  let query ← match fields.get? "query" with
    | some (.str q) => pure q
    | _ => throw "query must be a string"
  let operationName ← match fields.get? "operationName" with
    | none | some .null => pure none
    | some (.str name) => pure (some name)
    | _ => throw "operationName must be a string or null"
  let variables ← match fields.get? "variables" with
    | none | some .null => pure []
    | some (.obj vars) => vars.toList.mapM fun (k, v) => return (k, ← toInput 32 v)
    | _ => throw "variables must be an object or null"
  if let some extensions := fields.get? "extensions" then
    match extensions with
    | .null | .obj _ => pure ()
    | _ => throw "extensions must be an object or null"
  return ⟨query, operationName, variables⟩

end GraphQL.HttpJson

import GraphQL.Value

namespace GraphQL.Derive

private def lit (s : String) : String := reprStr s
private def ident (s : String) : String := "«" ++ s ++ "»"
private def member (s : String) : String := ident ("gql_" ++ s)
-- Escape Lean's special declaration name injectively, including the escape prefix itself.
private def typeIdent (s : String) : String :=
  ident (if s == "_root_" || s.startsWith "SDL_" then "SDL_" ++ s else s)
private def list (xs : List String) : String := "[" ++ String.intercalate ", " xs ++ "]"
private def typeName (p n : String) : String := p ++ ".Types." ++ typeIdent n
private def helper (p n : String) : String := p ++ ".Helpers." ++ ident n
private def argsName (p owner field : String) : String := p ++ ".Args." ++ ident (owner ++ "." ++ field)

private def typeCode : TypeRef → String
  | .named n r => s!"(.named {lit n} {r})"
  | .list t r => s!"(.list {typeCode t} {r})"

private def fieldCode (f : Field) : String :=
  s!"(⟨{lit f.name}, {typeCode f.type}, {list (f.arguments.map fun a => s!"⟨{lit a.name}, {typeCode a.type}⟩")}⟩ : _root_.GraphQL.Field)"

private def schemaCode (s : Schema) : String :=
  let types := s.types.map fun t =>
    let kind := match t.kind with
      | .scalar => "scalar" | .enumType => "enumType" | .input => "input"
      | .object => "object" | .interface => "interface" | .union => "union"
    s!"(⟨{lit t.name}, .{kind}, {list (t.fields.map fieldCode)}, {list (t.members.map lit)}, {list (t.implements.map lit)}⟩ : _root_.GraphQL.TypeDef)"
  s!"(⟨{list types}, {lit s.query}⟩ : _root_.GraphQL.Schema)"

private def atomType (s : Schema) (p n : String) : String :=
  if n == "String" || n == "ID" then "_root_.String"
  else if n == "Int" then "_root_.Int32"
  else if n == "Boolean" then "_root_.Bool"
  else match s.find? n with
    | some t => if t.kind == .object then s!"(_root_.GraphQL.Ref {lit n})"
      else if t.kind == .scalar then "_root_.String" else typeName p n
    | none => "_root_.Unit"

private def hostType (s : Schema) (p : String) : TypeRef → String
  | .named n r => if r then atomType s p n else s!"(_root_.Option {atomType s p n})"
  | .list t r => let inner := s!"(_root_.List {hostType s p t})"
    if r then inner else s!"(_root_.Option {inner})"

private def argType (s : Schema) (p : String) (t : TypeRef) : String :=
  if t.isRequired then hostType s p t else s!"(_root_.GraphQL.Presence {hostType s p t.require})"

private def decode (s : Schema) (p fuel : String) : TypeRef → String
  | .named n r =>
    let base := if n == "String" then "_root_.GraphQL.inputString"
      else if n == "ID" then "_root_.GraphQL.inputID"
      else if n == "Int" then "_root_.GraphQL.inputInt"
      else if n == "Boolean" then "_root_.GraphQL.inputBool"
      else match s.find? n with
        | some t => if t.kind == .scalar then "_root_.GraphQL.inputString"
          else if t.kind == .input then s!"({helper p ("decode." ++ n)} {fuel})"
          else helper p ("decode." ++ n)
        | none => "_root_.GraphQL.inputString"
    if r then base else s!"(_root_.GraphQL.inputOptional {base})"
  | .list t r =>
    let base := s!"(_root_.GraphQL.inputList {decode s p fuel t})"
    if r then base else s!"(_root_.GraphQL.inputOptional {base})"

private def decodeArg (s : Schema) (p fuel args name : String) (t : TypeRef) : String :=
  let fn := if t.isRequired then "requiredArgument" else "optionalArgument"
  s!"(← _root_.GraphQL.{fn} {args} {lit name} {decode s p fuel t.require})"

private def encode (s : Schema) (p : String) (t : TypeRef) (value : String) : String :=
  let wrap (r : Bool) (body : String → String) :=
    if r then body value else s!"(match {value} with | .none => _root_.GraphQL.RawValue.null | .some present => {body "present"})"
  match t with
  | .named n r => wrap r fun v =>
    if n == "String" || n == "ID" then s!"(_root_.GraphQL.RawValue.string {v})"
    else if n == "Int" then s!"(_root_.GraphQL.RawValue.int ({v}).toInt)"
    else if n == "Boolean" then s!"(_root_.GraphQL.RawValue.boolean {v})"
    else match s.find? n with
      | some t => if t.kind == .object then s!"(_root_.GraphQL.RawValue.object {lit n} ({v}).key)"
        else if t.kind == .scalar then s!"(_root_.GraphQL.RawValue.string {v})"
        else s!"({helper p ("encode." ++ n)} {v})"
      | none => "_root_.GraphQL.RawValue.null"
  | .list item r => wrap r fun v =>
    s!"(_root_.GraphQL.RawValue.list (({v}).map (fun element => {encode s p item "element"})))"

/-- SDL names occupy Types, Args and Objects; helper names use dots, absent from SDL names.
    Resolver records and dispatch are grouped by object, avoiding one enormous flat record. -/
def commands (namespaceName fullName : String) (s : Schema) : List String := Id.run do
  let p := "_root_." ++ fullName
  let mut result := [s!"namespace {namespaceName}", s!"def rawSchema : _root_.GraphQL.Schema := {schemaCode s}",
    "def schema : _root_.GraphQL.CheckedSchema := ⟨rawSchema, by decide +kernel⟩"]
  for t in s.types do
    if t.kind == .enumType then
      result := result ++ [s!"inductive Types.{typeIdent t.name} where\n" ++ String.intercalate "\n" (t.members.map fun n => s!"  | {member n}")]
      result := result ++ [s!"def Helpers.{ident ("encode." ++ t.name)} : {typeName p t.name} → _root_.GraphQL.RawValue\n" ++
        String.intercalate "\n" (t.members.map fun n => s!"  | .{member n} => .enumValue {lit n}")]
      result := result ++ [s!"def Helpers.{ident ("decode." ++ t.name)} : _root_.GraphQL.InputValue → _root_.Except _root_.String {typeName p t.name}\n" ++
        String.intercalate "\n" (t.members.map fun n => s!"  | .enumValue {lit n} => .ok .{member n}") ++ s!"\n  | _ => .error {lit ("expected enum " ++ t.name)}"]
    if t.kind == .interface || t.kind == .union then
      let members := s.types.filter (fun a => s.possibleType t.name a.name) |>.map (·.name)
      result := result ++ [s!"inductive Types.{typeIdent t.name} where\n" ++
        String.intercalate "\n" (members.map fun n => s!"  | {member n} (ref : _root_.GraphQL.Ref {lit n})")]
      let body := if members.isEmpty then " (value : " ++ typeName p t.name ++ ") : _root_.GraphQL.RawValue := nomatch value"
        else s!" : {typeName p t.name} → _root_.GraphQL.RawValue\n" ++
          String.intercalate "\n" (members.map fun n => s!"  | .{member n} ref => .object {lit n} ref.key")
      result := result ++ [s!"def Helpers.{ident ("encode." ++ t.name)}" ++ body]
  let inputs := s.types.filter (·.kind == .input)
  if !inputs.isEmpty then
    let localTypes (code : String) := inputs.foldl
      (fun acc t => acc.replace (typeName p t.name) (typeIdent t.name)) code
    let localDecoders (code : String) := inputs.foldl
      (fun acc t => acc.replace (helper p ("decode." ++ t.name)) (ident ("decode." ++ t.name))) code
    let decls := inputs.map fun t =>
      s!"inductive {typeIdent t.name} where\n  | mk " ++ String.intercalate " "
        (t.fields.map fun f => s!"({ident ("input." ++ f.name)} : {localTypes (argType s p f.type)})")
    result := result ++ ["namespace Types", "mutual\n" ++ String.intercalate "\n" decls ++ "\nend", "end Types"]
    let decoders := inputs.map fun t =>
      s!"def {ident ("decode." ++ t.name)} : _root_.Nat → _root_.GraphQL.InputValue → _root_.Except _root_.String {typeName p t.name}\n" ++
      "  | 0, _ => .error \"input depth limit exceeded\"\n" ++
      "  | fuel + 1, .object fields => do\n    return .mk " ++
      String.intercalate " " (t.fields.map fun f => localDecoders (decodeArg s p "fuel" "fields" f.name f.type)) ++
      s!"\n  | _, _ => .error {lit ("expected input object " ++ t.name)}"
    result := result ++ ["namespace Helpers", "mutual\n" ++ String.intercalate "\n" decoders ++ "\nend", "end Helpers"]
  let objects := s.types.filter (·.kind == .object)
  for t in objects do
    for f in t.fields do
      if !f.arguments.isEmpty then
        result := result ++ [s!"structure Args.{ident (t.name ++ "." ++ f.name)} where\n" ++
          String.intercalate "\n" (f.arguments.map fun a => s!"  {member a.name} : {argType s p a.type}")]
        result := result ++ [s!"def Helpers.{ident ("decode.args." ++ t.name ++ "." ++ f.name)} (fields : _root_.List (_root_.String × _root_.GraphQL.InputValue)) : _root_.Except _root_.String {argsName p t.name f.name} := do\n" ++
          "  return { " ++ String.intercalate ", " (f.arguments.map fun a => s!"{member a.name} := {decodeArg s p "128" "fields" a.name a.type}") ++ " }"]
    result := result ++ [s!"structure Objects.{typeIdent t.name} (m : Type → Type) where\n" ++
      String.intercalate "\n" (t.fields.map fun f =>
        let args := if f.arguments.isEmpty then "_root_.Unit" else argsName p t.name f.name
        s!"  {member f.name} : _root_.GraphQL.Ref {lit t.name} → {args} → m (_root_.Except _root_.String {hostType s p f.type})")]
    let cases := t.fields.map fun f =>
      let decodeArgs := if f.arguments.isEmpty then "(_root_.Except.ok () : _root_.Except _root_.String _root_.Unit)"
        else s!"{helper p ("decode.args." ++ t.name ++ "." ++ f.name)} call.arguments"
      s!"  | {lit f.name} => do\n    match {decodeArgs} with\n" ++
      "    | .error e => return .error e\n" ++
      s!"    | .ok args =>\n      let result ← resolvers.{member f.name} ⟨call.parent⟩ args\n" ++
      s!"      return result.map (fun value => {encode s p f.type "value"})"
    result := result ++ [s!"def Helpers.{ident ("dispatch." ++ t.name)} [_root_.Monad m] (resolvers : {p}.Objects.{typeIdent t.name} m) (call : _root_.GraphQL.Call) : m (_root_.Except _root_.String _root_.GraphQL.RawValue) :=\n" ++
      "  match call.field.name with\n" ++ String.intercalate "\n" cases ++ "\n  | _ => pure (.error \"unregistered field\")"]
  result := result ++ ["structure Resolvers (m : Type → Type) where\n" ++
    String.intercalate "\n" (objects.map fun t => s!"  {member t.name} : {p}.Objects.{typeIdent t.name} m")]
  result := result ++ [s!"def dispatch [_root_.Monad m] (resolvers : {p}.Resolvers m) (call : _root_.GraphQL.Call) : m (_root_.Except _root_.String _root_.GraphQL.RawValue) :=\n" ++
    "  match call.owner with\n" ++ String.intercalate "\n" (objects.map fun t =>
      s!"  | {lit t.name} => {helper p ("dispatch." ++ t.name)} resolvers.{member t.name} call") ++
    "\n  | _ => pure (.error \"unregistered object\")", s!"end {namespaceName}"]
  return result

open Lean Elab Command

syntax (name := graphqlSchema) "graphql_schema " ident str : command

elab_rules : command
  | `(graphql_schema $ns:ident $source:str) => do
    let schema ← match parseSchema source.getString with
      | .ok s => pure s
      | .error message => throwErrorAt source "{message}"
    unless checkSchema schema do
      throwErrorAt source "invalid schema: check root, unique/reserved names, referenced kinds, union members and interface fields"
    let fullName := ((← getCurrNamespace) ++ ns.getId).toString
    for command in commands ns.getId.toString fullName schema do
      let command := if command.startsWith "namespace " || command.startsWith "end " then command
        else "set_option maxRecDepth 20000 in set_option maxHeartbeats 8000000 in " ++ command
      match Parser.runParserCategory (← getEnv) `command command with
      | .error e => throwError "schema generator failed: {e}\n{command}"
      | .ok stx => elabCommand stx

end GraphQL.Derive

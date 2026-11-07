import Example.Resolvers

open GraphQL

def expectQuery (label query expected : String) (variables : Inputs := []) : IO Unit := do
  match demoQuery query variables with
  | .error message => throw (IO.userError s!"{label}: unexpected request error: {message}")
  | .ok actual => unless actual == expected do
      throw (IO.userError s!"{label}\nexpected: {expected}\nactual:   {actual}")
  IO.println s!"PASS {label}"

def expectRejected (label query : String) : IO Unit := do
  match demoQuery query with
  | .error _ => IO.println s!"PASS {label}"
  | .ok value => throw (IO.userError s!"{label}: unexpectedly accepted {value}")

def main : IO Unit := do
  expectQuery "ordered aliases and recursive objects"
    "{ z: greeting person: user(id: \"1\") { name friends { id name } role joined } }"
    r#"{"data":{"z":"Hello from Lean","person":{"name":"Ada","friends":[{"id":"2","name":"Grace"}],"role":"ADMIN","joined":"2026-11-01"}}}"#
  expectQuery "abstract types and inline fragments"
    "{ node { __typename id ... on User { name } } search { __typename ... on User { name } ... on Team { label } } }"
    r#"{"data":{"node":{"__typename":"User","id":"1","name":"Ada"},"search":[{"__typename":"User","name":"Ada"},{"__typename":"Team","label":"Research"}]}}"#
  expectQuery "nullable resolver failure preserves sibling"
    "{ broken greeting }"
    r#"{"data":{"broken":null,"greeting":"Hello from Lean"},"errors":[{"message":"example resolver failure","path":["broken"]}]}"#
  expectQuery "nullable list catches non-null element failure with alias path"
    "{ people: optionalUsers { nickname: risky } greeting }"
    r#"{"data":{"people":null,"greeting":"Hello from Lean"},"errors":[{"message":"user field failed","path":["people",1,"nickname"]}]}"#
  expectQuery "non-null list bubbles to root exactly once"
    "{ users { risky } greeting }"
    r#"{"data":null,"errors":[{"message":"user field failed","path":["users",1,"risky"]}]}"#
  expectQuery "merge repeated fields without losing selection order"
    "{ user(id: \"1\") { name } user(id: \"1\") { id } }"
    r#"{"data":{"user":{"name":"Ada","id":"1"}}}"#
  expectQuery "missing and null remain distinct"
    "{ a: optional b: optional(value: null) c: optional(value: \"text\") }"
    r#"{"data":{"a":"missing","b":"null","c":"text"}}"#
  expectQuery "recursive input coercion"
    "{ echo(filter: { query: \"find\" children: [{query: \"child\"}] }) }"
    r#"{"data":{"echo":"find:1"}}"#
  expectQuery "variables and defaults"
    "query Lookup($id: ID! = \"1\") { user(id: $id) { name } }"
    r#"{"data":{"user":{"name":"Ada"}}}"#
  expectQuery "missing nullable variable preserves omission"
    "query($value: String) { optional(value: $value) }"
    r#"{"data":{"optional":"missing"}}"#
  expectQuery "argument coercion failure is a field error"
    "query($v: Int = 1) { number(a: $v) greeting }"
    r#"{"data":{"number":null,"greeting":"Hello from Lean"},"errors":[{"message":"null supplied for a non-null input","path":["number"]}]}"#
    [("v", .null)]
  expectQuery "conditional directives"
    "query($show: Boolean!) { greeting broken @skip(if: true) user(id: 1) @include(if: $show) { name } }"
    r#"{"data":{"greeting":"Hello from Lean"}}"# [("show", .boolean false)]
  expectQuery "escaped strings"
    "{ optional(value: \"line\\nquote\\\"\") }"
    r#"{"data":{"optional":"line\u000aquote\""}}"#
  expectQuery "raw tab in GraphQL string"
    "{ optional(value: \"a\tb\") }"
    r#"{"data":{"optional":"a\u0009b"}}"#
  for (label, query) in [
    ("quoted brace cannot be syntax", "query \"{\" greeting }"),
    ("quoted colon cannot be syntax", "{ x \":\" greeting }"),
    ("number cannot touch name", "{ number(a:1b:2) }"),
    ("number cannot touch exponent", "{ number(a:1e5) }"),
    ("number cannot touch minus", "{ number(a:1-2) }"),
    ("disjoint branches still need the same shape", "{ search { ... on User { x: name } ... on Team { x: id } } }"),
    ("nullable directive variable is outside profile", "query($s:Boolean=true) { greeting @skip(if:$s) broken }"),
    ("unknown field", "{ nonexistent }"),
    ("missing required argument", "{ user { name } }"),
    ("undefined variable", "{ user(id: $id) { name } }"),
    ("incompatible variable", "query($id: Int!) { user(id: $id) { name } }"),
    ("non-null argument literal", "{ number(a: null) }"),
    ("32-bit integer range", "{ number(a: 2147483648) }"),
    ("integer leading zero", "{ number(a: 01) }"),
    ("conflicting alias", "{ x: greeting x: broken }"),
    ("invalid union selection", "{ search { id } }"),
    ("inapplicable fragment", "{ user(id: 1) { ... on Team { label } } }"),
    ("missing composite selection", "{ user(id: 1) }"),
    ("scalar subselection", "{ greeting { name } }"),
    ("invalid input field", "{ echo(filter: { unknown: true }) }"),
    ("duplicate input field", "{ echo(filter: { query: \"a\" query: \"b\" }) }"),
    ("duplicate directive", "{ greeting @skip(if: true) @skip(if: false) }"),
    ("invalid directive inside fragment", "{ user(id: 1) { ... on User { name @skip(if: 1) } } }"),
    ("unused variable", "query($unused: String) { greeting }"),
    ("unsupported mutation", "mutation { greeting }"),
    ("unsupported multiple operations", "query A { greeting } query B { greeting }")
  ] do expectRejected label query
  let .ok plan := prepare Demo.schema "{ user(id: 1) { name } user(id: 1) { id } }"
    | throw (IO.userError "cannot prepare merge count fixture")
  let .ok machine := execute plan | throw (IO.userError "cannot execute merge count fixture")
  let resolver (call : Call) : StateM Nat (Except String RawValue) := do
    if call.owner == "Query" && call.field.name == "user" then modify (· + 1)
    Demo.dispatch demoResolvers call
  let (_, count) := (drive resolver machine).run 0
  unless count == 1 do throw (IO.userError s!"merged resolver invoked {count} times")
  IO.println "PASS merged resolver is invoked once"
  expectQuery "disjoint aliases with matching response shape"
    "{ search { ... on User { x: name } ... on Team { x: label } } }"
    r#"{"data":{"search":[{"x":"Ada"},{"x":"Research"}]}}"#
  let wide := "{ " ++ String.intercalate " " ((List.range 300).map fun i => s!"a{i}: greeting") ++ " }"
  let .ok _ := prepare Demo.schema wide | throw (IO.userError "300 sibling selections should validate")
  IO.println "PASS 300 sibling selections have independent depth"
  let excessive := "{ " ++ String.intercalate " " ((List.range 500).map fun i => s!"a{i}: greeting") ++ " }"
  match prepare Demo.schema excessive with
  | .error e => unless e.contains "validation work" do throw (IO.userError e)
  | .ok _ => throw (IO.userError "validation work budget did not apply")
  IO.println "PASS shared validation work limit"
  let listQuery := "{ echo(filter:{children:[" ++ String.intercalate "," (List.replicate 300 "{query: \"]\"}") ++ "]}) }"
  expectQuery "300 list items and punctuation inside strings" listQuery
    r#"{"data":{"echo":"missing:300"}}"#
  let .ok parsed := parseOperation "{ greeting(a: [\"]\", \"}\", \":\", \"query\"]) }"
    | throw (IO.userError "string delimiters confused with syntax")
  let [.field _ _ [("a", .list values)] _ _ _] := parsed.selections
    | throw (IO.userError "unexpected parsed input list")
  unless values == [.string "]", .string "}", .string ":", .string "query"] do
    throw (IO.userError "wrong string list values")
  IO.println "PASS token kinds are preserved in lists"
  for source in [
    "input I { a(x: Int!): Int } type Query { q(i:I): String }",
    "interface I { a: Int } input X implements I { a: Int } type Query { q: String }",
    "enum E { true null } type Query { q: E }",
    "enum E { __private } type Query { q: E }",
    "type Query { q(__private: Int): String }",
    "scalar Float type Query { q: Float }"
  ] do
    match parseSchema source with
    | .error _ => pure ()
    | .ok schema => if checkSchema schema then throw (IO.userError s!"invalid SDL accepted: {source}")
  IO.println "PASS six invalid SDL forms rejected"
  IO.println "All prototype semantic tests passed."

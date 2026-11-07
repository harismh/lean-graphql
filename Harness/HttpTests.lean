import Harness.Http

namespace Harness.HttpTests
open Harness Http

partial def select (value : Lean.Json) (path : List String) : IO Lean.Json := do
  match path with
  | [] => pure value
  | key :: rest =>
    let child ← match value with
      | .arr _ =>
        let some n := key.toNat? | throw (IO.userError "Invalid JSON array index")
        index value n
      | _ => field value key
    select child rest

def get (r : Response) (path : List String) : IO Lean.Json := do select (← r.json) path

def certified : IO Unit := do
  let count ← IO.mkRef 0
  let check (label : String) (condition : Bool) : IO Unit := do
    Harness.check label condition
    count.modify (· + 1)
  withServer "graphql-certified" "normal" fun port => do
    let simple := query "{ projects { title } }"
    let r ← request port simple
    check "authorized ordered tenant-1 response" (r.status == 200 && r.body == r#"{"data":{"projects":[{"title":"left"},{"title":"right"},{"title":"first"},{"title":"second"}]}}"#)
    check "response headers" ((r.header "content-type").startsWith "application/graphql-response+json" && r.header "cache-control" == "no-store" && r.header "vary" == "Accept")
    let r ← request port {simple with auth := "Bearer tenant-2"}
    check "tenant-2 isolation" (r.status == 200 && (← r.json) == (← json r#"{"data":{"projects":[{"title":"secret"}]}}"#))
    let r ← request port (query "{ projects { tasks { project { title } } } }")
    let errors ← array (← get r ["errors"])
    let paths ← errors.mapM (fun e => field e "path")
    check "batch errors preserve filtered occurrence paths" (r.status == 200 && .arr paths == (← json r#"[["projects",0,"tasks",2,"project"],["projects",1,"tasks",0,"project"],["projects",1,"tasks",1,"project"]]"#))
    check "non-null fault bubbles to root" ((← get r ["data"]) == .null)
    let r ← request port (query "query Q($id: ID!) { project(id: $id) { title } }" [("variables", obj [("id", str "shared")]), ("operationName", str "Q")])
    check "variables and operation selection" (r.status == 200 && (← get r ["data", "project", "title"]) == str "first")
    let r ← request port (query "query Q($id: ID = \"shared\") { project(id: $id) { title } }" [("variables", obj [("id", .null)])])
    check "argument fault is execution response" (r.status == 200 && (← get r ["errors", "0", "path"]) == .arr #[str "project"])
    let cases : List (String × Request × Nat × String) := [
      ("GET", {method := "GET"}, 405, "POST required"),
      ("media", {simple with accept := "text/plain"}, 406, "No acceptable response media type"),
      ("content type", {simple with content := "text/plain"}, 415, "JSON content type required"),
      ("body bound", {body := String.ofList (List.replicate 65537 ' ')}, 413, "Request body too large"),
      ("JSON", {body := "{"}, 400, "Invalid JSON request"),
      ("duplicate JSON keys", {body := r#"{"query":"x","query":"y"}"#}, 400, "Invalid JSON request"),
      ("envelope", {body := "{\"query\":1}"}, 400, "Invalid request envelope"),
      ("parse", query "{", 400, "Invalid query syntax"),
      ("schema", query "{ nonexistent }", 422, "Invalid operation"),
      ("selection", query "{ projects { title } }" [("operationName", str "wrong")], 422, "Operation name does not match"),
      ("variables", query "query Q($id: ID!) { project(id: $id) { title } }", 422, "Invalid variable values"),
      ("auth", {simple with auth := "wrong"}, 401, "Authentication required")]
    for (label, input, status, message) in cases do
      let r ← request port input
      check label (r.status == status && (← r.json) == obj [("errors", .arr #[obj [("message", str message)]])])
    let r ← request port {simple with accept := "application/json"}
    check "JSON negotiation" (r.status == 200 && (r.header "content-type").startsWith "application/json")
  for (mode, status, message) in [("auth-throw", 500, "Internal error"), ("snapshot-throw", 500, "Internal error"),
      ("snapshot-none", 503, "Snapshot unavailable"), ("backend-throw", 503, "Backend unavailable"), ("transport", 503, "Backend unavailable")] do
    withServer "graphql-certified" mode fun port => do
      let r ← request port (query "{ projects { title } }")
      check (mode ++ " redaction") (r.status == status && !contains r.body "SECRET" &&
        (← r.json) == obj [("errors", .arr #[obj [("message", str message)]])])
      let r ← request port {body := "{"}
      check (mode ++ " preparation before effects") (r.status == 400 && (← r.json) == obj [("errors", .arr #[obj [("message", str "Invalid JSON request")]])])
  let total ← count.get
  ensure (total == 30) s!"Certified HTTP inventory changed: expected 30, executed {total}"
  IO.println s!"All {total} certified HTTP checks passed."

def legacy : IO Unit := do
  let count ← IO.mkRef 0
  let check (label : String) (condition : Bool) : IO Unit := do
    Harness.check label condition
    count.modify (· + 1)
  withServer "graphql-demo" "normal" fun port => do
    let greeting := query "{ greeting }"
    let r ← request port (query "{ z: greeting a: user(id: 1) { name } }")
    check "real POST and ordered response" (r.status == 200 && r.body == r#"{"data":{"z":"Hello from Lean","a":{"name":"Ada"}}}"#)
    check "GraphQL response media type" ((r.header "content-type").startsWith "application/graphql-response+json")
    let r ← request port (query "{ broken greeting }")
    check "IO exception remains a field error" (r.status == 200 && (← get r ["data", "greeting"]) == str "Hello from Lean" && (← get r ["data", "broken"]) == .null)
    check "private exception details are hidden" ((← get r ["errors", "0", "message"]) == str "internal resolver error" && !contains r.body "private")
    let r ← request port (query "query($v: Int = 1) { number(a: $v) greeting }" [("variables", obj [("v", .null)])])
    check "argument coercion error preserves data" (r.status == 200 && (← get r ["errors", "0", "path"]) == .arr #[str "number"] && (← get r ["data", "greeting"]) == str "Hello from Lean")
    let r ← request port {body := r#"{"query":"query($v: Int!) { number(a: $v) }","variables":{"v":1.0}}"#}
    check "integral JSON decimal coerces to Int" (r.status == 200 && (← get r ["data", "number"]) == num 1)
    let r ← request port (query "{ user { name } }")
    check "validation errors have no data" (r.status == 422 && ((← r.json).getObjVal? "data").toOption.isNone)
    let cases : List (String × Request × Nat) := [
      ("malformed JSON", {body := "{"}, 400),
      ("wrong envelope", {body := "{\"query\":4}"}, 422),
      ("duplicate decoded JSON keys", {body := r#"{"query":"{ greeting }","\u0071uery":"{ broken }"}"#}, 400),
      ("oversized body", {body := String.ofList (List.replicate 65537 ' ')}, 413),
      ("bounded JSON depth", {body := "{\"query\":\"{ greeting }\",\"variables\":{\"v\":" ++ String.ofList (List.replicate 33 '[') ++ "0" ++ String.ofList (List.replicate 33 ']') ++ "}}"}, 400),
      ("bounded JSON exponent", {body := r#"{"query":"{ greeting }","variables":{"v":1e9999999}}"#}, 400),
      ("invalid document", query "{", 400),
      ("operation selection", query "query A { greeting }" [("operationName", str "B")], 422),
      ("variable coercion", query "query($id: ID!) { user(id:$id) { name } }" [("variables", obj [])], 422)]
    for (label, input, status) in cases do
      check label ((← request port input).status == status)
    check "unsupported request media" ((← request port {greeting with content := "text/plain"}).status == 415)
    check "unsupported response media" ((← request port {greeting with accept := "text/html"}).status == 406)
    for (label, accept) in [
      ("explicit q=0 overrides wildcard", "application/graphql-response+json;q=0, */*;q=0.5"),
      ("Accept quality preference", "application/json;q=1, application/graphql-response+json;q=0.5"),
      ("Accept weight parameter is case insensitive", "application/graphql-response+json;Q=0, application/json;Q=0.5")] do
      let r ← request port {greeting with accept}
      check label (r.status == 200 && (r.header "content-type").startsWith "application/json")
    for text in ["query \"{\" greeting }", "{ x \":\" greeting }", "{ number(a:1b:2) }", "{ number(a:1e5) }", "{ number(a:1-2) }"] do
      let r ← request port (query text)
      check ("malformed tokens rejected before validation: " ++ text) (r.status == 400 && ((← r.json).getObjVal? "data").toOption.isNone)
    let r ← request port (query "{ user { name } }")
    check "validation diagnostics reach the client" (r.status == 422 && contains r.body "missing required argument 'id'")
    let r ← request port (query "{ search { ... on User { x: name } ... on Team { x: id } } }")
    check "disjoint response shapes are checked" (r.status == 422 && contains r.body "incompatible response shape")
    let r ← request port (query "query($s:Boolean=true){ greeting @skip(if:$s) broken }" [("variables", obj [("s", .null)])])
    check "nullable directive variable rejected before execution" (r.status == 422 && contains r.body "Boolean!" && ((← r.json).getObjVal? "data").toOption.isNone)
    let r ← request port (query "{ optional(value: \"a\tb\") }")
    check "raw tab in GraphQL string" (r.status == 200 && (← get r ["data", "optional"]) == str "a\tb")
    let nested := "{ user(id:1){" ++ String.join (List.replicate 30 "... on User{friends{") ++ "name" ++ String.join (List.replicate 30 "}}") ++ "}}"
    let started ← IO.monoMsNow
    let r ← request port (query nested)
    let elapsed := (← IO.monoMsNow) - started
    check "nested fragment validation stays bounded" (r.status == 200 && elapsed < 2000)
    IO.println s!"Nested fragment depth 30: {elapsed} ms (including client process)"
    let jobs ← (List.range 8).mapM fun _ => IO.asTask (request port (query nested)) .dedicated
    let foreground ← request port greeting
    let replies ← jobs.mapM (fun task => IO.ofExcept task.get)
    check "nested fragment traffic preserves responsiveness" (foreground.status == 200 && replies.all (fun r => r.status == 200))
    let wide := "{ " ++ String.intercalate " " ((List.range 500).map fun i => s!"a{i}: greeting") ++ " }"
    let r ← request port (query wide)
    check "validation work limit returns a diagnostic" (r.status == 422 && contains r.body "validation work")
    let r ← request port {method := "GET"}
    check "POST-only method policy" (r.status == 405 && r.header "allow" == "POST")
    discard <| Harness.run (← IO.appPath).toString #["--disconnect", toString port,
      "POST /graphql HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/json\r\nContent-Length: 10000\r\n\r\n{"] 5000
    let r ← request port greeting
    check "server recovers after incomplete-body disconnect" (r.status == 200 && contains r.body "Hello from Lean")
  let total ← count.get
  ensure (total == 35) s!"Legacy HTTP inventory changed: expected 35, executed {total}"
  IO.println s!"All {total} legacy HTTP checks passed."

end Harness.HttpTests

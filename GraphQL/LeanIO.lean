import GraphQL.Execution
import GraphQL.HttpJson
import LeanIO

namespace GraphQL.LeanIO

open Std Http Async

private def trim (s : String) : String := s.trimAscii.toString

private def quality (parts : List String) : Nat := Id.run do
  for p in parts do
    let p := (trim p).toLower
    if p.startsWith "q=" then
      let q := (p.drop 2).toString
      if q == "1" || q == "1.0" || q == "1.00" || q == "1.000" then return 1000
      if q == "0" then return 0
      if q.startsWith "0." then
        let digits := (q.drop 2).toString
        if digits.length > 3 || digits.isEmpty then return 0
        return digits.toNat?.getD 0 * 10 ^ (3 - digits.length)
      return 0
  return 1000

def chooseMedia (accept : String) : Option String := Id.run do
  let mut best : Option (String × Nat) := none
  for media in ["application/graphql-response+json", "application/json"] do
    let mut chosen : Option (Nat × Nat) := none
    for item in accept.splitOn "," do
      let parts := item.splitOn ";"
      let name := trim (parts.headD "") |>.toLower
      let specificity := if name == media then 2 else if name == "application/*" then 1 else 0
      if name == media || name == "application/*" || name == "*/*" then
        let q := quality parts.tail
        match chosen with
        | none => chosen := some (specificity, q)
        | some (oldSpec, oldQ) => if specificity > oldSpec || (specificity == oldSpec && q > oldQ) then
            chosen := some (specificity, q)
    if let some (_, q) := chosen then
      if q > 0 && q > (best.map (·.2)).getD 0 then best := some (media, q)
  return best.map (·.1)

private def respond (status : Status) (media body : String) (allow : Bool := false) : ContextAsync (Response Body.Any) := do
  let builder := Response.new.status status
    |>.header! "content-type" (media ++ "; charset=utf-8")
    |>.header! "vary" "Accept"
    |>.header! "cache-control" "no-store"
  let builder := if allow then builder.header! "allow" "POST" else builder
  let response ← builder.fromBytes body.toUTF8
  return (response : Response Body.Any)

private def readBody (request : Request Body.Stream) : ContextAsync (Except IO.Error String) := do
  try
    let text ← request.body.readAll (maximumSize := some 65536)
    pure (.ok text)
  catch e => pure (.error e)

/-- POST-only P0 adapter. Execution responses use a documented HTTP 200 compatibility
    policy; this is not a claim of full current GraphQL-over-HTTP draft conformance. -/
def handler (schema : CheckedSchema) (resolve : Call → ContextAsync (Except String RawValue)) :
    _root_.LeanIO.Router.HandlerFn := fun request => do
  let accept := (request.line.headers.get? (.ofString! "accept")).map (·.value) |>.getD "*/*"
  let some media := chooseMedia accept | return ← respond .notAcceptable "application/json" (requestError "no acceptable response media type")
  if request.line.method != .post then
    return ← respond .methodNotAllowed media (requestError "this prototype supports POST only") true
  let content := (request.line.headers.get? (.ofString! "content-type")).map (·.value) |>.getD ""
  unless (trim ((content.splitOn ";").headD "")).toLower == "application/json" do
    return ← respond .unsupportedMediaType media (requestError "Content-Type must be application/json")
  let bodyResult ← readBody request
  let .ok body := bodyResult |
    let tooLarge := match bodyResult with
      | .error (.userError text) => text.startsWith "body exceeded"
      | _ => false
    respond (if tooLarge then .payloadTooLarge else .badRequest) media
      (requestError (if tooLarge then "request body exceeds 65536 bytes" else "cannot read request body"))
  if let .error e := HttpJson.checkEnvelope body then
    return ← respond .badRequest media (requestError e)
  let .ok json := Lean.Json.parse body | return ← respond .badRequest media (requestError "invalid JSON body")
  let .ok envelope := HttpJson.decode json | return ← respond .unprocessableEntity media (requestError "invalid GraphQL request envelope or variable value")
  let plan ← match prepareDetailed schema envelope.query with
    | .ok plan => pure plan
    | .error e => return ← respond (match e with | .parse _ => .badRequest | .validation _ => .unprocessableEntity) media (requestError e.message)
  if let some requested := envelope.operationName then
    unless plan.operation.name == some requested do
      return ← respond .unprocessableEntity media (requestError "operationName does not match this operation")
  let machine ← match execute plan envelope.variables with
    | .ok machine => pure machine
    | .error e => return ← respond .unprocessableEntity media (requestError e)
  let safeResolve (call : Call) : ContextAsync (Except String RawValue) := do
    try resolve call catch _ => return .error "internal resolver error"
  let result ← drive safeResolve machine
  respond .ok media (encodeCompletion result)

def routes (schema : CheckedSchema) (resolve : Call → ContextAsync (Except String RawValue)) :
    _root_.LeanIO.Router.Router :=
  _root_.LeanIO.Router.Router.empty
    |>.addRoute (_root_.LeanIO.Router.Route.new .post "/graphql" (handler schema resolve))
    |>.addRoute (_root_.LeanIO.Router.Route.new .get "/graphql" (handler schema resolve))

end GraphQL.LeanIO

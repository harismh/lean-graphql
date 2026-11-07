import Example.Tenant.CertifiedHandler

namespace Example.Tenant.Http
open Std Async
open Protocol Handler

/-- The only bodies accepted by the HTTP sender. -/
abbrev Outbound (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (credential : String) :=
  {reply : Reply // PublicReply reply ∨ ∃ request,
    request.credential = credential ∧ GoodReply AuthSound AcquireSound request reply}

def publicOutbound (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (failure : Failure)
    (media : Media := .json) : Outbound AuthSound AcquireSound credential :=
  ⟨(publicReply failure media).val, .inl (publicReply failure media).property⟩

def status : Protocol.Status → Std.Http.Status
  | .ok => .ok | .badRequest => .badRequest | .unauthorized => .unauthorized
  | .methodNotAllowed => .methodNotAllowed | .notAcceptable => .notAcceptable
  | .tooLarge => .payloadTooLarge | .unsupportedMedia => .unsupportedMediaType
  | .unprocessable => .unprocessableEntity | .unavailable => .serviceUnavailable
  | .internal => .internalServerError

def respond (result : Outbound AuthSound AcquireSound credential) : ContextAsync (Std.Http.Response Std.Http.Body.Any) := do
  let reply := result.val
  let builder := Std.Http.Response.new.status (status reply.status)
    |>.header! "content-type" (reply.media.name ++ "; charset=utf-8")
    |>.header! "vary" "Accept"
    |>.header! "cache-control" "no-store"
  let builder := if reply.status == .methodNotAllowed then builder.header! "allow" "POST" else builder
  let response ← builder.fromBytes reply.bytes
  return (response : Std.Http.Response Std.Http.Body.Any)

def header (request : Std.Http.Request Std.Http.Body.Stream) (name : String) (fallback : String := "") : String :=
  (request.line.headers.get? (.ofString! name)).map (·.value) |>.getD fallback

def receive (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (authenticate : Authenticate ContextAsync AuthSound)
    (acquire : Acquire ContextAsync AcquireSound) (backend : BackendFactory ContextAsync)
    (request : Std.Http.Request Std.Http.Body.Stream) :
    ContextAsync (Outbound AuthSound AcquireSound (header request "authorization")) := do
  let media := (negotiate (header request "accept" "*/*")).getD .json
  try
    if (negotiate (header request "accept" "*/*")).isNone then return publicOutbound AuthSound AcquireSound .media
    if request.line.method != .post then return publicOutbound AuthSound AcquireSound .method media
    let content := header request "content-type"
    if (((content.splitOn ";").headD "").trimAscii.toString.toLower) != "application/json" then
      return publicOutbound AuthSound AcquireSound .contentType media
    let body ← try request.body.readAll (maximumSize := some 65536) catch error =>
      let tooLarge := match error with
        | IO.Error.userError text => text.startsWith "body exceeded"
        | _ => false
      return publicOutbound AuthSound AcquireSound (if tooLarge then .bodyLimit else .bodyRead) media
    let input : Protocol.Request := ⟨"POST", header request "accept" "*/*", content, body, header request "authorization"⟩
    let result ← runTenantProgram (ε := IO.Error) AuthSound AcquireSound authenticate acquire backend input
    return ⟨result.val, .inr ⟨input, rfl, result.property⟩⟩
  catch _ => return publicOutbound AuthSound AcquireSound .internal media

def handler (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (authenticate : Authenticate ContextAsync AuthSound)
    (acquire : Acquire ContextAsync AcquireSound) (backend : BackendFactory ContextAsync) :
    _root_.LeanIO.Router.HandlerFn := fun request => do
  respond (← receive AuthSound AcquireSound authenticate acquire backend request)

def routes (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (authenticate : Authenticate ContextAsync AuthSound)
    (acquire : Acquire ContextAsync AcquireSound) (backend : BackendFactory ContextAsync) : _root_.LeanIO.Router.Router :=
  _root_.LeanIO.Router.Router.empty
    |>.addRoute (_root_.LeanIO.Router.Route.new .post "/graphql" (handler AuthSound AcquireSound authenticate acquire backend))
    |>.addRoute (_root_.LeanIO.Router.Route.new .get "/graphql" (handler AuthSound AcquireSound authenticate acquire backend))

theorem outbound_certified (result : Outbound AuthSound AcquireSound credential) :
    PublicReply result.val ∨ ∃ request, request.credential = credential ∧
      GoodReply AuthSound AcquireSound request result.val := result.property

end Example.Tenant.Http

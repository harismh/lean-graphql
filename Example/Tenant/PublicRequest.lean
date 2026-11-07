import Example.Tenant.WireResponse
import GraphQL.LeanIO

namespace Example.Tenant.Protocol
open GraphQL.Plan GraphQL.Plan.InputCoercion Preparation

inductive Media where
  | graphql | json
  deriving DecidableEq, Repr

def Media.name : Media → String
  | .graphql => "application/graphql-response+json"
  | .json => "application/json"

inductive Status where
  | ok | badRequest | unauthorized | methodNotAllowed | notAcceptable
  | tooLarge | unsupportedMedia | unprocessable | unavailable | internal
  deriving DecidableEq, Repr

inductive Failure where
  | media | method | contentType | bodyLimit | bodyRead | json | envelope | parse
  | validation | operation | variables | authentication | snapshot | transport | internal
  deriving DecidableEq, Repr

def Failure.message : Failure → String
  | .media => "No acceptable response media type"
  | .method => "POST required"
  | .contentType => "JSON content type required"
  | .bodyLimit => "Request body too large"
  | .bodyRead => "Cannot read request body"
  | .json => "Invalid JSON request"
  | .envelope => "Invalid request envelope"
  | .parse => "Invalid query syntax"
  | .validation => "Invalid operation"
  | .operation => "Operation name does not match"
  | .variables => "Invalid variable values"
  | .authentication => "Authentication required"
  | .snapshot => "Snapshot unavailable"
  | .transport => "Backend unavailable"
  | .internal => "Internal error"

def Failure.status : Failure → Status
  | .media => .notAcceptable
  | .method => .methodNotAllowed
  | .contentType => .unsupportedMedia
  | .bodyLimit => .tooLarge
  | .bodyRead | .json | .parse | .envelope => .badRequest
  | .validation | .operation | .variables => .unprocessable
  | .authentication => .unauthorized
  | .snapshot | .transport => .unavailable
  | .internal => .internal

structure Request where
  method : String
  accept : String := "*/*"
  contentType : String := "application/json"
  body : String
  credential : String := ""

structure Ready where
  operation : InputSurface.Operation
  prepared : Prepared operation
  supplied : Supplied
  environment : Environment
  interpreted : VariablesMeaning supplied operation.variables environment
  media : Media

def negotiate (accept : String) : Option Media :=
  match GraphQL.LeanIO.chooseMedia accept with
  | some "application/graphql-response+json" => some .graphql
  | some "application/json" => some .json
  | _ => none

/-- This pure phase has no principal, snapshot, backend or exception payload. -/
def prepareRequest (request : Request) : Except Failure Ready := do
  let some media := negotiate request.accept | throw .media
  if request.method != "POST" then throw .method
  if (((request.contentType.splitOn ";").headD "").trimAscii.toString.toLower) != "application/json" then throw .contentType
  if request.body.utf8ByteSize > 65536 then throw .bodyLimit
  let _ ← (GraphQL.HttpJson.checkEnvelope request.body).mapError (fun _ => Failure.json)
  let json ← (Lean.Json.parse request.body).mapError (fun _ => Failure.json)
  let envelope ← (GraphQL.HttpJson.decode json).mapError (fun _ => Failure.envelope)
  if envelope.query.length > 32768 then throw .validation
  let parsed ← (GraphQL.parseOperation envelope.query).mapError (fun _ => Failure.parse)
  if let some name := envelope.operationName then
    if parsed.name != some name then throw .operation
  let operation := decodeOperation parsed
  let prepared ← (prepare operation).mapError (fun _ => Failure.validation)
  let supplied := envelope.variables.map (fun (name, value) => (name, decodeRaw value))
  match interpreted : variables supplied operation.variables with
  | .error _ => throw .variables
  | .ok environment => return ⟨operation, prepared, supplied, environment, variables_sound _ _ _ interpreted, media⟩

structure Reply where
  status : Status
  media : Media
  bytes : ByteArray

/-- Closed public error vocabulary. No arbitrary string enters this envelope. -/
def FailureValue (failure : Failure) : GraphQL.ResponseValue :=
  .object [("errors", .array [.object [("message", .string failure.message)]])]

def PublicFailureBytes (failure : Failure) (bytes : ByteArray) : Prop :=
  WireEncoding.EncodesBytes (FailureValue failure) bytes

def PublicReply (reply : Reply) : Prop :=
  ∃ failure, reply.status = failure.status ∧ PublicFailureBytes failure reply.bytes

def publicReply (failure : Failure) (media : Media := .json) : {reply : Reply // PublicReply reply} :=
  ⟨⟨failure.status, media, (FailureValue failure).encode.toUTF8⟩,
    failure, rfl, WireEncoding.encode_bytes_correct _⟩

theorem ready_valid (ready : Ready) : InputSurface.ValidOperation ready.operation ∧
    InputSurface.InProfile ready.operation ∧ InputSurface.WithinLimits ready.operation := prepare_sound ready.prepared

end Example.Tenant.Protocol

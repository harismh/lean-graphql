import Example.Tenant.PublicRequest

namespace Example.Tenant.Handler
open GraphQL GraphQL.Plan GraphQL.Plan.InputCoercion Preparation CertifiedExecution Protocol

/-- The real-caller connection is an explicit parameter. The implementation must
produce evidence for the identity it returns; no fact about opaque auth is assumed. -/
abbrev Authenticate (m : Type → Type) (AuthSound : String → Principal → Prop) :=
  (credential : String) → m (Option {principal : Principal // AuthSound credential principal})

abbrev Acquire (m : Type → Type) (AcquireSound : Principal → Snapshot → Prop) :=
  (principal : Principal) → m (Option {snapshot : Snapshot // AcquireSound principal snapshot})
abbrev BackendFactory (m : Type → Type) := Binding.Request → Transport m

inductive GoodReply (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (request : Protocol.Request) : Reply → Prop where
  | publicFailure (valid : PublicReply reply) : GoodReply AuthSound AcquireSound request reply
  | application (ready : Ready) (accepted : prepareRequest request = .ok ready)
      (authenticated : AuthSound request.credential principal)
      (acquired : AcquireSound principal snapshot)
      (interpreted : VariablesMeaning ready.supplied ready.operation.variables environment)
      (keyMeaning : KeyMeaning (InputSurface.rootArgument ready.operation.selection) environment key)
      (authorized : Wire.AuthorizedWireResponse snapshot principal
        (instantiate key ready.prepared.template.val ready.prepared.template.property).selection bytes) :
      GoodReply AuthSound AcquireSound request ⟨.ok, ready.media, bytes⟩

abbrev CertifiedReply (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (request : Protocol.Request) :=
  {reply : Reply // GoodReply AuthSound AcquireSound request reply}

def publicResult (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (request : Protocol.Request)
    (failure : Failure) (media : Media := .json) : CertifiedReply AuthSound AcquireSound request :=
  ⟨(publicReply failure media).val, .publicFailure (publicReply failure media).property⟩

/-- Application bytes are tied to the exact acquired snapshot and principal. -/
inductive CoreGood (ready : Ready) (context : Binding.Request) : Reply → Prop where
  | publicFailure (valid : PublicReply reply) : CoreGood ready context reply
  | application
      (interpreted : VariablesMeaning ready.supplied ready.operation.variables environment)
      (keyMeaning : KeyMeaning (InputSurface.rootArgument ready.operation.selection) environment key)
      (authorized : Wire.AuthorizedWireResponse context.snapshot context.principal
        (instantiate key ready.prepared.template.val ready.prepared.template.property).selection bytes) :
      CoreGood ready context ⟨.ok, ready.media, bytes⟩

abbrev CoreReply (ready : Ready) (context : Binding.Request) :=
  {reply : Reply // CoreGood ready context reply}

def coreFailure (ready : Ready) (context : Binding.Request) (failure : Failure) : CoreReply ready context :=
  ⟨(publicReply failure ready.media).val, .publicFailure (publicReply failure ready.media).property⟩

def authenticatedCore [Monad m] [MonadExceptOf ε m]
    (ready : Ready) (context : Binding.Request)
    (backend : Transport m) : m (CoreReply ready context) := do
  let result ← CertifiedBatchExecution.runPreparedTransport
    (Generated.adapter Generated.application) Generated.application_agreement
    (redactTransport (ε := ε) backend) ready.prepared context ready.supplied 2 (by decide)
  match result with
  | .error _ => return coreFailure ready context .transport
  | .ok result =>
    match result with
    | ⟨.error _, guarantee⟩ => nomatch (show False from by
        cases guarantee with
        | rejected rejected =>
          have impossible := (variables_complete ready.interpreted).symm.trans (variables_rejected_complete rejected)
          cases impossible)
    | ⟨.ok response, guarantee⟩ =>
      have evidence : ∃ environment key,
          VariablesMeaning ready.supplied ready.operation.variables environment ∧
          KeyMeaning (InputSurface.rootArgument ready.operation.selection) environment key ∧
          Spec.AuthorizedResponse context.snapshot context.principal
            (instantiate key ready.prepared.template.val ready.prepared.template.property).selection response := by
        cases guarantee with
        | response variables key authorized => exact ⟨_, _, variables, key, authorized⟩
      return ⟨⟨.ok, ready.media, Wire.encode response⟩, by
        obtain ⟨environment, key, variables, keyMeaning, authorized⟩ := evidence
        exact .application variables keyMeaning ⟨response, authorized, Wire.encode_correct response⟩⟩

theorem core_exact_inputs (result : CoreReply ready context) :
    CoreGood ready context result.val := result.property

def promote (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop) (request : Protocol.Request)
    (ready : Ready) (accepted : prepareRequest request = .ok ready)
    (principal : {principal : Principal // AuthSound request.credential principal}) (snapshot : {snapshot : Snapshot // AcquireSound principal.val snapshot})
    (result : CoreReply ready ⟨snapshot.val, principal.val⟩) : CertifiedReply AuthSound AcquireSound request :=
  ⟨result.val, by
    obtain ⟨reply, proof⟩ := result
    cases proof with
    | publicFailure valid => exact .publicFailure valid
    | application variables key authorized =>
      exact .application ready accepted principal.property snapshot.property variables key authorized⟩

/-- Prepare/coerce, authenticate, acquire exactly one immutable snapshot, execute,
encode. All caught failures discard exception payloads. No raw resolver route. -/
def runTenantProgram [Monad m] [MonadExceptOf ε m]
    (AuthSound : String → Principal → Prop) (AcquireSound : Principal → Snapshot → Prop)
    (authenticate : Authenticate m AuthSound)
    (acquire : Acquire m AcquireSound) (backend : BackendFactory m) (request : Protocol.Request) :
    m (CertifiedReply AuthSound AcquireSound request) :=
  match accepted : prepareRequest request with
  | .error failure => pure (publicResult AuthSound AcquireSound request failure (negotiate request.accept |>.getD .json))
  | .ok ready => do
    try
      let some principal ← authenticate request.credential |
        return publicResult AuthSound AcquireSound request .authentication ready.media
      let some snapshot ← acquire principal.val |
        return publicResult AuthSound AcquireSound request .snapshot ready.media
      let result ← authenticatedCore (ε := ε) ready ⟨snapshot.val, principal.val⟩ (backend ⟨snapshot.val, principal.val⟩)
      return promote AuthSound AcquireSound request ready accepted principal snapshot result
    catch _ => return publicResult AuthSound AcquireSound request .internal ready.media

theorem returned_bytes_certified (result : CertifiedReply AuthSound AcquireSound request) :
    GoodReply AuthSound AcquireSound request result.val := result.property

/-- A concrete authenticated identity policy for the in-memory demo. Production
identity services must supply their own justified AuthSound evidence. -/
def DemoAuthSound (credential : String) (principal : Principal) : Prop :=
  (credential = "Bearer tenant-1" ∧ principal.tenant = 1) ∨
  (credential = "Bearer tenant-2" ∧ principal.tenant = 2)

def demoAuthenticate [Monad m] : Authenticate m DemoAuthSound := fun credential =>
  if first : credential = "Bearer tenant-1" then pure (some ⟨⟨1⟩, Or.inl ⟨first, rfl⟩⟩)
  else if second : credential = "Bearer tenant-2" then pure (some ⟨⟨2⟩, Or.inr ⟨second, rfl⟩⟩)
  else pure none

def DemoAcquireSound (_ : Principal) (snapshot : Snapshot) : Prop := snapshot = S4bProofs.request.snapshot

def demoAcquire [Monad m] : Acquire m DemoAcquireSound := fun _ => pure (some ⟨S4bProofs.request.snapshot, rfl⟩)

def demoBackend [Monad m] : BackendFactory m := fun _ =>
  transportBackend (adapterBackend (Generated.adapter Generated.application) Generated.application_agreement)

end Example.Tenant.Handler

import Example.Tenant.Http
import Example.Tenant.S6cProofs

namespace Example.Tenant.S6dProofs
open GraphQL.Plan Handler Protocol
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

structure Counts where
  auth : Nat := 0
  snapshot : Nat := 0
  calls : Nat := 0
  deriving Repr, DecidableEq
abbrev TestM := ExceptT String (StateM Counts)

def authenticate : Authenticate TestM DemoAuthSound := fun credential => do
  modify fun c => {c with auth := c.auth + 1}
  demoAuthenticate credential

def acquire : Acquire TestM DemoAcquireSound := fun principal => do
  modify fun c => {c with snapshot := c.snapshot + 1}
  demoAcquire principal

def backend : BackendFactory TestM := fun context call pre => do
  modify fun c => {c with calls := c.calls + 1}
  demoBackend context call pre

def input (body : String) (credential := "Bearer tenant-1") : Protocol.Request :=
  {method := "POST", body, credential}

def run (request : Protocol.Request) :=
  ((runTenantProgram (ε := String) DemoAuthSound DemoAcquireSound authenticate acquire backend request).run).run {}

def simple := input "{\"query\":\"{ projects { title } }\"}"
def batched := input "{\"query\":\"{ projects { tasks { project { title } } } }\"}"
def missingVariable := input "{\"query\":\"query Q($id: ID!) { project(id: $id) { title } }\"}"

/-- Conditional on the public preparation result; parser fidelity is tested separately. -/
theorem rejected_before_effects (request : Protocol.Request) (failure : Failure)
    (rejected : prepareRequest request = .error failure) : (run request).2 = {} := by
  unfold run runTenantProgram
  split
  · rfl
  · rename_i ready accepted
    rw [rejected] at accepted
    cases accepted

theorem foreign_snapshot_answer_rejected : ¬ Fault.Post (Planning.branchId .taskProject)
    S4bProofs.otherRequest S4bProofs.sharedTask () (.ok S4bProofs.firstTarget) := by
  intro valid
  rcases valid with ⟨wrong, _⟩ | ⟨code, wrong⟩
  · have different := S4bProofs.cross_scope_reuse_rejected
    apply different
    exact wrong
  · cases wrong

theorem unacquired_snapshot_rejected (principal : Principal) :
    ¬ DemoAcquireSound principal S4bProofs.otherRequest.snapshot := by
  change ¬ S4bProofs.otherRequest.snapshot = S4bProofs.request.snapshot
  decide +kernel

theorem wrong_authenticated_tenant : ¬ DemoAuthSound "Bearer tenant-1" ⟨2⟩ := by
  simp [DemoAuthSound]

def nativeTests : IO Unit := do
  for request in [simple, batched, {simple with credential := "Bearer tenant-2"}] do
    let result ← runTenantProgram (ε := IO.Error) DemoAuthSound DemoAcquireSound demoAuthenticate demoAcquire demoBackend request
    unless result.val.status == .ok do throw (IO.userError "S6d request failed")
    let .ok _ := Lean.Json.parse (String.fromUTF8! result.val.bytes) |
      throw (IO.userError "S6d response is invalid JSON")
  let explodingAuth : Authenticate IO DemoAuthSound := fun _ => throw (IO.userError "SECRET")
  let result ← runTenantProgram (ε := IO.Error) DemoAuthSound DemoAcquireSound explodingAuth demoAcquire demoBackend simple
  unless result.val.bytes == (publicReply .internal).val.bytes do throw (IO.userError "S6d auth exception leaked")
  let explodingAcquire : Acquire IO DemoAcquireSound := fun _ => throw (IO.userError "SECRET")
  let result ← runTenantProgram (ε := IO.Error) DemoAuthSound DemoAcquireSound demoAuthenticate explodingAcquire demoBackend simple
  unless result.val.bytes == (publicReply .internal).val.bytes do throw (IO.userError "S6d snapshot exception leaked")
  let explodingBackend : BackendFactory IO := fun _ _ _ => throw (IO.userError "SECRET")
  let result ← runTenantProgram (ε := IO.Error) DemoAuthSound DemoAcquireSound demoAuthenticate demoAcquire explodingBackend simple
  unless result.val.bytes == (publicReply .transport).val.bytes do throw (IO.userError "S6d backend exception leaked")
  unless (run (input "{")).2 == {} && (run simple).2.auth == 1 && (run simple).2.snapshot == 1 &&
      (run (input simple.body "wrong")).2 == ⟨1, 0, 0⟩ do
    throw (IO.userError "S6d authentication/acquisition ordering mismatch")
  unless (run missingVariable).2 == {} && (run batched).2.calls == 9 do
    throw (IO.userError "S6d preparation/batching effects mismatch")
  IO.println "S6d: exact-input core, authentication, one snapshot, early rejection and exception redaction passed."

end Example.Tenant.S6dProofs

import Example.Tenant.CertifiedExecution

namespace Example.Tenant.S6aProofs
open GraphQL GraphQL.Plan GraphQL.Plan.InputCoercion Planning Preparation CertifiedExecution
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

/-- Real state effects; later answers can differ from earlier answers. -/
def statefulBackend : Backend (StateM Nat) := fun call permitted => do
  let counter ← get
  let outcome := S4Proofs.varyingResolver counter call
  set outcome.2
  return ⟨outcome.1, S4Proofs.varying_resolver_permitted counter call permitted⟩

def statefulResult := (runPrepared statefulBackend S5Proofs.prepared S4bProofs.request [("id", .string "shared")]).run 0

theorem stateful_execution_certified : Guarantee S5Proofs.prepared S4bProofs.request [("id", .string "shared")] statefulResult.1.val :=
  statefulResult.1.property

def statefulFaultResult := (runPrepared statefulBackend S5Proofs.prepared S4bProofs.request [("id", .string "shared")]).run 1

theorem stateful_fault_certified : Guarantee S5Proofs.prepared S4bProofs.request [("id", .string "shared")] statefulFaultResult.1.val :=
  statefulFaultResult.1.property

theorem stateful_fault_observed : (statefulFaultResult.1.val.toOption.map (fun response => response.errors.length)) = some 1 := rfl

theorem stateful_calls : statefulResult.2 = 2 := rfl

theorem variable_failure_no_effects :
    ((runPrepared statefulBackend S5Proofs.prepared S4bProofs.request []).run 41).2 = 41 := rfl

theorem argument_failure_no_effects :
    ((runPrepared statefulBackend S5Proofs.defaultPrepared S4bProofs.request [("id", .null)]).run 41).2 = 41 := rfl

theorem pure_driver_preserves_s5 :
    (runPrepared (m := Id) (adapterBackend S4bProofs.adapter Generated.application_agreement)
      S5Proofs.prepared S4bProofs.request [("id", .string "shared")]).val =
      runMachine (Batch.driver S4bProofs.adapter)
        (execute S4bProofs.adapter S5Proofs.prepared S4bProofs.request [("id", .string "shared")] 2 (by decide)) :=
  pure_prepared_eq_s5 _ _ _ _ _ (by decide)

/-- A real batch primitive followed by another call. This tests the driver
boundary, not the as-yet-unproved optimized tenant plan. -/
def batchThenCall : Batching.Exec Unit :=
  .pending (.batch Binding.rootProjects S4bProofs.request (Vector.replicate 2 ((), ())))
    (fun _ => .pending (.one Binding.rootProjects S4bProofs.request () ()) (fun _ => .done ()))

theorem batch_then_call_contract : Sat Fault.contracts.Pre Fault.contracts.Post batchThenCall (fun _ => True) :=
  ⟨⟨trivial, fun _ => trivial⟩, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩

def failingTransport : Transport (StateM Nat) := fun _ _ => do
  modify (· + 1)
  pure (.error .unavailable)

theorem batch_transport_aborts :
    (driveTransport failingTransport batchThenCall batch_then_call_contract).run 0 = (.error .unavailable, 1) := by
  unfold batchThenCall
  simp only [driveTransport.eq_2, driveTransport.eq_1]
  rfl

def faultMeanings : Meanings schema Binding.carriers Binding.Request ApplicationError :=
  fun _ _ _ _ => .error (.framework .internal)

theorem fault_meanings_permitted : BackendSatisfies Fault.contracts faultMeanings := by
  intro owner field request parent args pre
  exact Or.inr ⟨.internal, rfl⟩

def perKeyFaults : Backend (StateM Nat) := fun call pre => do
  modify (· + 1)
  return ⟨denoteCall faultMeanings call, call_contract _ _ fault_meanings_permitted call pre⟩

theorem per_key_fault_continues :
    ((driveTransport (transportBackend perKeyFaults) batchThenCall batch_then_call_contract).run 0).2 = 2 := by
  unfold batchThenCall
  simp only [driveTransport.eq_2, driveTransport.eq_1]
  rfl

def secretException (secret : String) : Transport (Except String) := fun _ _ => .error secret

theorem exception_redacted (secret : String) :
    driveTransport (redactTransport (ε := String) (secretException secret)) batchThenCall batch_then_call_contract =
      .ok (.error .internal) := by
  unfold batchThenCall
  simp only [driveTransport.eq_2, driveTransport.eq_1]
  rfl

theorem exception_noninterference (first second : String) :
    driveTransport (redactTransport (ε := String) (secretException first)) batchThenCall batch_then_call_contract =
      driveTransport (redactTransport (ε := String) (secretException second)) batchThenCall batch_then_call_contract := rfl

/-- Native IO exceptions use the same redacting producer; messages are discarded. -/
def ioException : Transport IO := fun _ _ => throw (IO.userError "private database detail")

def nativeTests : IO Unit := do
  let result ← runPrepared (adapterBackend S4bProofs.adapter Generated.application_agreement)
    S5Proofs.prepared S4bProofs.request [("id", .string "shared")]
  unless result.val.toOption == (statefulResult.1.val).toOption do
    throw (IO.userError "S6a certified IO result mismatch")
  let failed ← runPreparedTransport (redactTransport (ε := IO.Error) ioException)
    S5Proofs.prepared S4bProofs.request [("id", .string "shared")]
  match failed with
  | .error .internal => pure ()
  | _ => throw (IO.userError "S6a exception was not a named transport failure")
  let rejected ← runPreparedTransport (redactTransport (ε := IO.Error) ioException) S5Proofs.prepared S4bProofs.request []
  match rejected with
  | .ok result => match result.val with
    | .error (.variable _) => pure ()
    | _ => throw (IO.userError "S6a request rejection mismatch")
  | .error _ => throw (IO.userError "S6a invalid variables reached backend")
  let batchFailed := (driveTransport failingTransport batchThenCall batch_then_call_contract).run 0
  unless batchFailed.2 == 1 do throw (IO.userError "S6a transport failure ran continuation")
  unless ((driveTransport (transportBackend perKeyFaults) batchThenCall batch_then_call_contract).run 0).2 == 2 do
    throw (IO.userError "S6a per-key faults were treated as transport failure")
  IO.println "S6a: certified IO/state drivers, early failures, batch abort, and exception redaction passed."

end Example.Tenant.S6aProofs

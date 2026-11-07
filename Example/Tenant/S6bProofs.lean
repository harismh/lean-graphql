import Example.Tenant.CertifiedBatchExecution

namespace Example.Tenant.S6bProofs
open GraphQL GraphQL.Plan Planning Batching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

abbrev adapter : Batching.Actual := S4bProofs.adapter
abbrev request := S4bProofs.request

def program := optimized generatedCapability request S4bProofs.child.val 2 (by decide)

theorem program_contract : Sat Fault.contracts.Pre Fault.contracts.Post program
    (Spec.AuthorizedResponse request.snapshot request.principal (selection (.field "title" [] .nil .nil))) :=
  BatchFault.optimized_contract adapter Generated.application_agreement generatedCapability request
    S4bProofs.child.val (by intro h; cases h) (by decide)

def inputSelection : InputSurface.Selection :=
  .field "projects" [] (.field "tasks" [] (.field "project" [] (.field "title" [] .nil .nil) .nil) .nil) .nil

def inputOperation : InputSurface.Operation := { variables := [], selection := inputSelection }

def prepared : Preparation.Prepared inputOperation :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, S4bProofs.selected⟩

def faultAnswers : (call : Call schema Binding.carriers Binding.Request) → Answer ApplicationError call
  | .one field context parent args => (adapter field).single context parent args
  | .batch field context (n := n) inputs => Vector.ofFn (fun i : Fin n =>
      if i.val = 0 then .error (.framework .internal) else (adapter field).single context (inputs.get i).1 (inputs.get i).2)

theorem fault_answers_permitted (call : Call schema Binding.carriers Binding.Request) (pre : Fault.contracts.Pre call) :
    Fault.contracts.Post call (faultAnswers call) := by
  cases call with
  | one field context parent args => exact CertifiedExecution.adapter_permitted adapter Generated.application_agreement _ pre
  | batch field context inputs =>
    intro i
    simp only [faultAnswers]
    simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
    split
    · exact Or.inr ⟨.internal, rfl⟩
    · exact Or.inl (Contract.tenantResolvers_satisfy_contracts adapter Generated.application_agreement field context
        (inputs.get i).1 (inputs.get i).2 (pre.2 i))

/-- Only batch positions fault; single calls still use the exact producer. -/
def perKeyBackend : CertifiedExecution.Backend (StateM Nat) := fun call pre => do
  modify (· + 1)
  return ⟨faultAnswers call, fault_answers_permitted call pre⟩

def failBatch : CertifiedExecution.Transport (StateM Nat) := fun call pre => do
  modify (· + 1)
  match call with
  | .batch .. => return .error .unavailable
  | .one .. => return .ok ⟨Batch.driver adapter call, CertifiedExecution.adapter_permitted adapter Generated.application_agreement call pre⟩

def faultRun := (driveCertified perKeyBackend program program_contract).run 0
def transportRun := (driveTransport failBatch program program_contract).run 0

theorem fault_run_authorized : Spec.AuthorizedResponse request.snapshot request.principal
    (selection (.field "title" [] .nil .nil)) faultRun.1.val := faultRun.1.property

theorem fault_run_conforms : Spec.Conforms (selection (.field "title" [] .nil .nil)) faultRun.1.val :=
  Fault.authorized_conforms fault_run_authorized

def transportStatus : Except TransportFailure α → Option TransportFailure
  | .error failure => some failure
  | .ok _ => none

theorem transport_aborts_optimized : transportRun.1 = .error .unavailable ∧ transportRun.2 = 6 := by
  constructor
  · have status : transportStatus transportRun.1 = some .unavailable := by decide +kernel
    cases result : transportRun.1 with
    | error error => simp [transportStatus, result] at status; cases status; rfl
    | ok value => simp [transportStatus, result] at status
  · decide +kernel

theorem per_key_continues_optimized : faultRun.2 = 7 := by decide +kernel

def path (parent task : Nat) : Spec.Path := [.field "projects", .index parent, .field "tasks", .index task, .field "project"]
def expectedErrors : List Spec.Error := [
  ⟨.framework .internal, path 0 0⟩, ⟨.framework .internal, path 0 1⟩,
  ⟨.application .unavailable, path 0 2⟩, ⟨.application .unavailable, path 1 0⟩,
  ⟨.framework .internal, path 1 1⟩]

theorem original_occurrence_paths : faultRun.1.val.errors = expectedErrors := by decide +kernel

/-- Fault injection before batching or in a child region, still with real Post
certificates. The non-faulting calls use the proved pure producer. -/
def faultAt (position : Nat) : CertifiedExecution.Backend (StateM Nat) := fun call pre => do
  let count ← get
  set (count + 1)
  let backend : Meanings schema Binding.carriers Binding.Request ApplicationError := if count = position then S6aProofs.faultMeanings else adapter.meanings
  have valid : BackendSatisfies Fault.contracts backend := by
    unfold backend
    split
    · exact S6aProofs.fault_meanings_permitted
    · intro owner field context parent args allowed
      exact Or.inl (Contract.tenantResolvers_satisfy_contracts adapter Generated.application_agreement field context parent args allowed)
  return ⟨denoteCall backend call, call_contract Fault.contracts backend valid call pre⟩

def rootFault := (driveCertified (faultAt 0) program program_contract).run 0
def preparationFault := (driveCertified (faultAt 1) program program_contract).run 0
def childFault := (driveCertified (faultAt 7) program program_contract).run 0

theorem root_fault_no_wave : rootFault.2 = 1 := by decide +kernel
theorem preparation_fault_smaller_wave : preparationFault.2 = 6 := by decide +kernel
theorem child_fault_keeps_remaining_calls : childFault.2 = 9 := by decide +kernel

theorem child_fault_path : childFault.1.val.errors.head? =
    some ⟨.framework .internal, path 0 0 ++ [.field "title"]⟩ := by decide +kernel

/-- The S5 operation entry now actually chooses the optimized certified Machine. -/
def preparedRun := (CertifiedBatchExecution.runPrepared adapter Generated.application_agreement perKeyBackend
  prepared request [] 2 (by decide)).run 0

theorem prepared_entry_uses_batch : preparedRun.2 = 7 := by decide +kernel

theorem prepared_entry_guarantee : CertifiedExecution.Guarantee prepared request [] preparedRun.1.val := preparedRun.1.property

def emptyPreparation : Batching.Prepared := ⟨.ok [], fun i => Fin.elim0 i⟩

theorem fabricated_preparation_rejected : ¬ BatchFault.PreparedEvidence request emptyPreparation := by
  intro valid
  rcases valid.1 with ⟨wrong, _⟩ | ⟨code, wrong⟩
  · have unequal : ([] : List Project) ≠ projects request.snapshot request.principal := by decide +kernel
    exact unequal (Except.ok.inj wrong)
  · cases wrong

theorem unkeyed_reuse_rejected : ¬ Fault.Post (branchId .taskProject) request
    ⟨"t3", 1, "three", "missing"⟩ () (.ok S4bProofs.firstTarget) := by
  intro valid
  rcases valid with ⟨wrong, _⟩ | ⟨code, wrong⟩
  · cases wrong
  · cases wrong

def emptyRequest : Binding.Request := { request with snapshot := { request.snapshot with tasks := [] } }
def emptyRun := (CertifiedBatchExecution.runPreparedTransport adapter Generated.application_agreement failBatch
  prepared emptyRequest [] 2 (by decide)).run 0

theorem empty_wave_no_batch : transportStatus emptyRun.1 = none ∧ emptyRun.2 = 5 := by decide +kernel

theorem variable_rejection_no_effects :
    ((CertifiedBatchExecution.runPrepared adapter Generated.application_agreement perKeyBackend
      S5Proofs.prepared request [] 2 (by decide)).run 41).2 = 41 := by decide +kernel

theorem argument_error_no_effects :
    ((CertifiedBatchExecution.runPrepared adapter Generated.application_agreement perKeyBackend
      S5Proofs.defaultPrepared request [("id", .null)] 2 (by decide)).run 41).2 = 41 := by decide +kernel

def nativeTests : IO Unit := do
  let result ← CertifiedBatchExecution.runPrepared adapter Generated.application_agreement
    (CertifiedExecution.adapterBackend adapter Generated.application_agreement) prepared request [] 2 (by decide)
  unless result.val.toOption == some (Runtime.run adapter request S4bProofs.selected) do
    throw (IO.userError "S6b optimized certified IO differs from reference")
  unless faultRun.1.val.errors == expectedErrors do throw (IO.userError "S6b shared faults lost original paths")
  unless faultRun.2 == 7 && transportRun.2 == 6 do throw (IO.userError "S6b batch failure control flow mismatch")
  match transportRun.1 with
  | .error .unavailable => pure ()
  | _ => throw (IO.userError "S6b whole-batch failure fabricated per-key results")
  unless rootFault.2 == 1 && preparationFault.2 == 6 && childFault.2 == 9 do
    throw (IO.userError "S6b preparation/child fault regression")
  IO.println "S6b: optimized fault contracts, certified IO, per-occurrence errors, and whole-batch abort passed."

end Example.Tenant.S6bProofs

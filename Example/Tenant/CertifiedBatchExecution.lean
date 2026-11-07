import Example.Tenant.BatchFaultExecution

namespace Example.Tenant.CertifiedBatchExecution
open GraphQL GraphQL.Plan GraphQL.Plan.InputCoercion Planning Preparation CertifiedExecution

/-- Planner capabilities supply key evidence, not effectful answers. The latter
come exclusively from the certified backend passed to the driver. -/
def runPrepared [Monad m] (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (backend : Backend m) (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied)
    (capacity : Nat) (positive : 0 < capacity) : m (Result prepared request supplied) :=
  match decoded : variables supplied operation.variables with
  | .error error => pure ⟨.error (.variable error), .rejected (variables_rejected_sound decoded)⟩
  | .ok environment => do
    let key := idKey (InputSurface.rootArgument operation.selection) environment
    let result ← driveCertified backend (executeKey adapter prepared request key capacity positive)
      (BatchFault.key_contract adapter agreement prepared request key positive)
    return ⟨.ok result.val, .response (variables_sound _ _ _ decoded) (key_sound _ _) result.property⟩

def runPreparedTransport [Monad m] (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (backend : Transport m) (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied)
    (capacity : Nat) (positive : 0 < capacity) : m (Except TransportFailure (Result prepared request supplied)) :=
  match decoded : variables supplied operation.variables with
  | .error error => pure (.ok ⟨.error (.variable error), .rejected (variables_rejected_sound decoded)⟩)
  | .ok environment => do
    let key := idKey (InputSurface.rootArgument operation.selection) environment
    match ← driveTransport backend (executeKey adapter prepared request key capacity positive)
      (BatchFault.key_contract adapter agreement prepared request key positive) with
    | .error failure => pure (.error failure)
    | .ok result => pure (.ok ⟨.ok result.val,
        .response (variables_sound _ _ _ decoded) (key_sound _ _) result.property⟩)

theorem rejected_without_backend [Monad m] (adapter : Batching.Actual)
    (agreement : BindingAgreement Binding.independentBindings adapter) (backend : Backend m)
    (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied)
    (positive : 0 < capacity) (rejected : VariablesRejected supplied operation.variables error) :
    runPrepared adapter agreement backend prepared request supplied capacity positive =
      pure ⟨.error (.variable error), Guarantee.rejected rejected⟩ := by
  unfold runPrepared
  split
  · congr 1
    apply Subtype.ext
    rename_i code decoded
    have equal := decoded.symm.trans (variables_rejected_complete rejected)
    cases equal
    rfl
  · rename_i environment decoded
    have impossible := decoded.symm.trans (variables_rejected_complete rejected)
    cases impossible

theorem transport_rejected_without_backend [Monad m] (adapter : Batching.Actual)
    (agreement : BindingAgreement Binding.independentBindings adapter) (backend : Transport m)
    (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied)
    (positive : 0 < capacity) (rejected : VariablesRejected supplied operation.variables error) :
    runPreparedTransport adapter agreement backend prepared request supplied capacity positive =
      pure (.ok ⟨.error (.variable error), Guarantee.rejected rejected⟩) := by
  unfold runPreparedTransport
  split
  · congr 1
    congr 1
    apply Subtype.ext
    rename_i code decoded
    have equal := decoded.symm.trans (variables_rejected_complete rejected)
    cases equal
    rfl
  · rename_i environment decoded
    have impossible := decoded.symm.trans (variables_rejected_complete rejected)
    cases impossible

theorem pure_eq_s5 (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied) (positive : 0 < capacity) :
    (runPrepared (m := Id) adapter agreement (adapterBackend adapter agreement) prepared request supplied capacity positive).val =
      runMachine (Batch.driver adapter) (execute adapter prepared request supplied capacity positive) := by
  unfold runPrepared execute
  split
  · rename_i error decoded
    simp only [decoded, runMachine]
    rfl
  · rename_i environment decoded
    simp only [decoded]
    change Except.ok (driveCertified (m := Id) (pureBackend _ _) _ _).val = _
    rw [drive_pure_value]
    simp only [run_bind, runMachine]

end Example.Tenant.CertifiedBatchExecution

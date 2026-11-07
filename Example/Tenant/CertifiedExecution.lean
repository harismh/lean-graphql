import Example.Tenant.S5Proofs
import GraphQL.Plan.CertifiedDriver

namespace Example.Tenant.CertifiedExecution
open GraphQL GraphQL.Plan GraphQL.Plan.InputCoercion Planning Preparation

abbrev Backend (m : Type → Type) := CertifiedBackend m Fault.contracts.Pre Fault.contracts.Post
abbrev Transport (m : Type → Type) := TransportBackend m Fault.contracts.Pre Fault.contracts.Post

/-- Fixed prepared operation, variable input, snapshot and principal. Success
certifies the instantiated selection; request failures have an independent reason. -/
inductive Guarantee (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied) :
    Except RequestError Spec.Response → Prop where
  | rejected (reason : VariablesRejected supplied operation.variables error) :
      Guarantee prepared request supplied (.error (.variable error))
  | response (variables : VariablesMeaning supplied operation.variables environment)
      (keyMeaning : KeyMeaning (InputSurface.rootArgument operation.selection) environment key)
      (authorized : Spec.AuthorizedResponse request.snapshot request.principal
        (instantiate key prepared.template.val prepared.template.property).selection response) :
      Guarantee prepared request supplied (.ok response)

abbrev Result (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied) :=
  {result : Except RequestError Spec.Response // Guarantee prepared request supplied result}

/-- This entry deliberately uses the S4 fault-certified machine. The optimized
S4b machine must obtain its own Sat theorem before it can use this entry. -/
def runPrepared [Monad m] (backend : Backend m) (prepared : Prepared operation)
    (request : Binding.Request) (supplied : Supplied) : m (Result prepared request supplied) :=
  match decoded : variables supplied operation.variables with
  | .error error => pure ⟨.error (.variable error), .rejected (variables_rejected_sound decoded)⟩
  | .ok environment => do
    let key := idKey (InputSurface.rootArgument operation.selection) environment
    let built := instantiate key prepared.template.val prepared.template.property
    let result ← driveCertified backend (executeResolved request built.resolved)
      (resolved_authorized request built.resolved (instantiated_nonempty built prepared.valid.1.1))
    return ⟨.ok result.val, .response (variables_sound _ _ _ decoded) (key_sound _ _) result.property⟩

/-- A whole-transport failure is outside the response and its per-field errors.
It does not run a resolver continuation with a fabricated answer. -/
def runPreparedTransport [Monad m] (backend : Transport m) (prepared : Prepared operation)
    (request : Binding.Request) (supplied : Supplied) : m (Except TransportFailure (Result prepared request supplied)) :=
  match decoded : variables supplied operation.variables with
  | .error error => pure (.ok ⟨.error (.variable error), .rejected (variables_rejected_sound decoded)⟩)
  | .ok environment => do
    let key := idKey (InputSurface.rootArgument operation.selection) environment
    let built := instantiate key prepared.template.val prepared.template.property
    match ← driveTransport backend (executeResolved request built.resolved)
        (resolved_authorized request built.resolved (instantiated_nonempty built prepared.valid.1.1)) with
    | .error failure => pure (.error failure)
    | .ok result => pure (.ok ⟨.ok result.val,
        .response (variables_sound _ _ _ decoded) (key_sound _ _) result.property⟩)

theorem rejected_without_backend [Monad m] (backend : Backend m) (prepared : Prepared operation)
    (request : Binding.Request) (supplied : Supplied)
    (rejected : VariablesRejected supplied operation.variables error) :
    runPrepared backend prepared request supplied =
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

theorem transport_rejected_without_backend [Monad m] (backend : Transport m) (prepared : Prepared operation)
    (request : Binding.Request) (supplied : Supplied)
    (rejected : VariablesRejected supplied operation.variables error) :
    runPreparedTransport backend prepared request supplied =
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

theorem response_conforms (prepared : Prepared operation) (result : Result prepared request supplied) (success : result.val = .ok response) :
    ∃ environment key, VariablesMeaning supplied operation.variables environment ∧
      KeyMeaning (InputSurface.rootArgument operation.selection) environment key ∧
      Spec.Conforms (instantiate key prepared.template.val prepared.template.property).selection response := by
  have guarantee := result.property
  rw [success] at guarantee
  cases guarantee with
  | response variables key authorized => exact ⟨_, _, variables, key, Fault.authorized_conforms authorized⟩

theorem adapter_permitted (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter) :
    ∀ call, Fault.contracts.Pre call → Fault.contracts.Post call (Batch.driver adapter call) := by
  intro call pre
  rw [Batch.driver_exact]
  apply call_contract Fault.contracts adapter.meanings _ call pre
  intro owner field request parent args valid
  exact Or.inl (Contract.tenantResolvers_satisfy_contracts adapter agreement field request parent args valid)

def adapterBackend [Monad m] (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter) : Backend m :=
  pureBackend (Batch.driver adapter) (adapter_permitted adapter agreement)

theorem pure_prepared_eq_s5 (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied) (positive : 0 < capacity) :
    (runPrepared (m := Id) (adapterBackend adapter agreement) prepared request supplied).val =
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
    rw [key_execution]

end Example.Tenant.CertifiedExecution

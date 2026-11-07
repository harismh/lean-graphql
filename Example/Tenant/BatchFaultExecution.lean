import Example.Tenant.BatchFaultFinish

namespace Example.Tenant.BatchFault
open GraphQL GraphQL.Plan Planning Batching
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Universal in permitted answers at every suspension, including preparation,
per-key batch faults and child-region faults. No deterministic-run argument. -/
theorem optimized_contract (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (batch : Batch.Eligible adapter (branchId .taskProject)) (request : Binding.Request)
    (child : IR.Resolved .project nested) (nonempty : nested ≠ .nil) (positive : 0 < capacity) :
    Sat Fault.contracts.Pre Fault.contracts.Post (optimized batch request child capacity positive)
      (Spec.AuthorizedResponse request.snapshot request.principal (selection nested)) := by
  unfold optimized
  apply sat_bind _ _ (prepare_contract request)
  intro prepared valid
  apply sat_bind _ _ (wave_contract adapter agreement batch request prepared valid positive)
  exact fun outcomes permitted => finish_contract request child nonempty prepared valid outcomes permitted

theorem execute_contract (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query surface) (nonempty : surface ≠ .nil) (positive : 0 < capacity) :
    Sat Fault.contracts.Pre Fault.contracts.Post (Batching.execute adapter request selected capacity positive)
      (Spec.AuthorizedResponse request.snapshot request.principal surface) := by
  unfold Batching.execute
  split
  · exact Fault.execution_authorized request selected nonempty
  · rename_i eligible accepted
    obtain ⟨nested, child, childNonempty, shape, batch⟩ := eligible
    cases shape
    exact optimized_contract adapter agreement batch request child.val childNonempty positive

theorem execute_conforms (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query surface) (nonempty : surface ≠ .nil) (positive : 0 < capacity) :
    Sat Fault.contracts.Pre Fault.contracts.Post (Batching.execute adapter request selected capacity positive)
      (Spec.Conforms surface) :=
  sat_weaken _ (execute_contract adapter agreement request selected nonempty positive) (fun _ => Fault.authorized_conforms)

theorem key_contract (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (prepared : Preparation.Prepared operation) (request : Binding.Request)
    (key : Except GraphQL.Plan.InputCoercion.Error String) (positive : 0 < capacity) :
    Sat Fault.contracts.Pre Fault.contracts.Post (Preparation.executeKey adapter prepared request key capacity positive)
      (Spec.AuthorizedResponse request.snapshot request.principal
        (Preparation.instantiate key prepared.template.val prepared.template.property).selection) := by
  unfold Preparation.executeKey
  split
  · exact execute_contract adapter agreement request _ (Preparation.instantiated_nonempty _ prepared.valid.1.1) positive
  · exact Preparation.resolved_authorized request _ (Preparation.instantiated_nonempty _ prepared.valid.1.1)

end Example.Tenant.BatchFault

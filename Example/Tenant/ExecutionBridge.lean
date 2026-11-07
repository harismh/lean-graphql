import Example.Tenant.PlanTransport
import Example.Tenant.BindingBridge
import Example.Tenant.LoweringCorrectness

namespace Example.Tenant.ExecutionBridge
open GraphQL.Plan Planning

abbrev ActualAdapter := Adapter Binding.indexedSchema.schema Binding.carriers Binding.Request ApplicationError

theorem adapter_transport (s : Snapshot) (adapter : ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter) :
    MeaningTransport (Binding.transport s) (fun p => (⟨s, p⟩ : Binding.Request))
      (meanings s) (Adapter.meanings adapter) := by
  intro object field principal parent args
  have target := adapter_single_agreement Binding.independentBindings adapter agreement
    object (Binding.checked.coordinate field) ⟨s, principal⟩ (Binding.transport s object parent) args
  have manual := adapter_single_agreement Binding.independentBindings (Binding.adapt Binding.application)
    Binding.application_agreement object (Binding.checked.coordinate field)
    ⟨s, principal⟩ (Binding.transport s object parent) args
  exact (target.trans manual.symm).trans
    (Binding.binding_agrees_s1 s principal object (Binding.checked.coordinate field) parent args)

def actualResponse (adapter : ActualAdapter) (request : Binding.Request)
    (selected : IR.Checked .query selection) : Spec.Response :=
  Spec.envelope (operationDenotes (Adapter.meanings adapter)
    (compileFor Binding.carriers Binding.Request selected.val) () request [])

theorem actual_response_eq (adapter : ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query selection) :
    actualResponse adapter request selected =
      Spec.EvalSpec (Spec.tenantMeanings request.snapshot request.principal) selection := by
  have transport := compiled_transport (Binding.transport request.snapshot)
    (fun p => (⟨request.snapshot, p⟩ : Binding.Request)) (meanings request.snapshot)
    (Adapter.meanings adapter) (adapter_transport request.snapshot adapter agreement)
    selected.val () request.principal []
  exact (congrArg Spec.envelope transport).trans (planned_response_eq selected)

theorem actual_response_authorized (adapter : ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query selection) (nonempty : selection ≠ .nil) :
    Spec.AuthorizedResponse request.snapshot request.principal selection (actualResponse adapter request selected) := by
  rw [actual_response_eq adapter agreement]
  exact Spec.eval_authorized ⟨nonempty, IR.resolved_valid selected.val⟩

theorem actual_response_conforms (adapter : ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query selection) (nonempty : selection ≠ .nil) :
    Spec.Conforms selection (actualResponse adapter request selected) := by
  rw [actual_response_eq adapter agreement]
  exact Spec.eval_conforms ⟨nonempty, IR.resolved_valid selected.val⟩

theorem every_valid_operation (adapter : ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (valid : ValidOperation selection) :
    ∃ selected, IR.lower .query selection = some selected ∧
      actualResponse adapter request selected =
        Spec.EvalSpec (Spec.tenantMeanings request.snapshot request.principal) selection := by
  obtain ⟨selected, lower⟩ := IR.lower_complete valid.2
  exact ⟨selected, lower, actual_response_eq adapter agreement request selected⟩

end Example.Tenant.ExecutionBridge

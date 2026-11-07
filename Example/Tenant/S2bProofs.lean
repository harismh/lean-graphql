import Example.Tenant.S4Proofs
import Example.Tenant.ArgumentProofs
import Example.Tenant.Generated
import Example.Tenant.GenerationFixture

namespace Example.Tenant.S2bProofs
open GraphQL.Plan

theorem generated_schema_pin : Generated.indexed.schema = Binding.indexedSchema.schema := rfl

theorem generated_layout_pin : Generated.indexed.argumentLayouts = Binding.indexedSchema.argumentLayouts := by
  funext owner field
  rcases owner with ⟨owner, bound⟩
  rcases owner with _ | (_ | (_ | owner)) <;>
    rcases field with _ | (_ | (_ | field)) <;>
    simp [Generated.indexed, Binding.indexedSchema] <;>
    simp [Binding.demoAst] at bound <;> omega

theorem tenant_argument_layout : Binding.checked.indexed.argumentLayouts 0 0 =
    [⟨"id", .named "ID" true⟩] := rfl

theorem generated_execution (request : Binding.Request)
    (selected : IR.Checked .query selection) :
    Runtime.run (Generated.adapter Generated.application) request selected =
      Spec.EvalSpec (Spec.tenantMeanings request.snapshot request.principal) selection :=
  Runtime.run_eq_spec _ Generated.application_agreement request selected

theorem generated_authorization (request : Binding.Request)
    (selected : IR.Checked .query selection) (nonempty : selection ≠ .nil) :
    Spec.AuthorizedResponse request.snapshot request.principal selection
      (Runtime.run (Generated.adapter Generated.application) request selected) :=
  Runtime.run_authorized _ Generated.application_agreement request selected nonempty

theorem generated_conformance (request : Binding.Request)
    (selected : IR.Checked .query selection) (nonempty : selection ≠ .nil) :
    Spec.Conforms selection (Runtime.run (Generated.adapter Generated.application) request selected) :=
  Runtime.run_conforms _ Generated.application_agreement request selected nonempty

theorem generated_tenant_view (request : Binding.Request)
    (selected : IR.Checked .query selection) :
    Runtime.run (Generated.adapter Generated.application) (View.request request) selected =
      Runtime.run (Generated.adapter Generated.application) request selected :=
  View.run_tenant_view _ Generated.application_agreement request selected

theorem generated_batch_slot :
    (Generated.adapter Generated.application Binding.taskProject).batch = some Binding.taskProjectBatch := rfl

end Example.Tenant.S2bProofs

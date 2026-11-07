import Example.Tenant.S2Proofs
open GraphQL.Plan Example.Tenant Example.Tenant.Binding Example.Tenant.S2Proofs
def altered : FieldBinding Example.Tenant.Binding.taskProject carriers Request ApplicationError :=
  ⟨(fun _ _ _ => .error (.application .unavailable)), some taskProjectBatch⟩

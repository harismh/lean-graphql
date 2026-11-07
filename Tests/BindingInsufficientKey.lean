import Example.Tenant.S2Proofs
open GraphQL.Plan Example.Tenant Example.Tenant.Binding Example.Tenant.S2Proofs
def badKey : SufficientKey (models := carriers) Example.Tenant.Binding.taskProject taskProjectSingle where
  Key := Unit
  equal := inferInstance
  key := fun _ _ _ => ()
  sufficient := by intros; rfl

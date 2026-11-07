import Example.Tenant.S4bProofs
open GraphQL.Plan Example.Tenant Example.Tenant.Planning

def missing : Batching.Actual := fun field => ⟨(S4bProofs.adapter field).single, none⟩
example : Batch.Eligible missing (branchId .taskProject) :=
  ⟨Binding.taskProjectBatch, rfl, Binding.taskProjectKey, rfl⟩

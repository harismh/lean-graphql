import Example.Tenant.S3Proofs
open Example.Tenant
example : Contract.tenant.post Binding.projectTitle S3Proofs.request Checks.ownedProject ()
    (.ok Checks.ownedProject.id) := by
  constructor
  · rfl
  · trivial

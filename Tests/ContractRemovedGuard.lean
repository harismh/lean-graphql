import Example.Tenant.S3Proofs
open Example.Tenant
example : Contract.AllowedOutcome S3Proofs.request Binding.rootProject.decl.output
    (.ok (some Checks.foreignProject)) := by
  intro row found
  cases found
  exact ⟨by decide, by decide⟩

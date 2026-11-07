import Example.Tenant.S6dProofs
open Example.Tenant GraphQL.Plan Planning
example : Fault.Post (branchId .taskProject) S4bProofs.otherRequest S4bProofs.sharedTask () (.ok S4bProofs.firstTarget) :=
  Or.inl ⟨by rfl, by simp [Contract.AllowedOutcome]⟩

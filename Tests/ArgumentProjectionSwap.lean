import Example.Tenant.ArgumentProofs
open GraphQL.Plan Example.Tenant
example : ArgumentProjectionAgreement ArgumentProofs.pairArguments ArgumentProofs.swappedPack := by
  intro value index
  rfl

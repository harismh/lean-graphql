import Example.Tenant.Compile
open GraphQL.Plan Example.Tenant Example.Tenant.Planning
def wrong : TenantNode ⟨[], []⟩ [Unit, Principal, String] Nat :=
  .call (branchId IR.Branch.project) (.there .here) .here (.there (.there .here))

import Example.Tenant.Compile
open GraphQL.Plan Example.Tenant Example.Tenant.Planning
def wrong : TenantNode ⟨[], []⟩ [String, Principal, String] (Outcome ApplicationError (Option (Occurrence ([] : List Project)))) :=
  .call (branchId IR.Branch.project) (.there .here) .here (.there (.there .here))

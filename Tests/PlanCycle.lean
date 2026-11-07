import Example.Tenant.Compile
open GraphQL.Plan Example.Tenant Example.Tenant.Planning
def wrong : TenantGraph ⟨[], []⟩ [] [String] :=
  .snoc wrong (.literal .string "cycle")

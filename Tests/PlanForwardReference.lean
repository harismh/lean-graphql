import Example.Tenant.Compile
open GraphQL.Plan Example.Tenant Example.Tenant.Planning
def wrong : TenantGraph ⟨[], []⟩ [] [String, String] :=
  .snoc (.snoc .nil (.literal .string "prior"))
    (.map (fun value : String => value) (.there .here))

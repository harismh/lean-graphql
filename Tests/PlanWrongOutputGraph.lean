import Example.Tenant.Compile
open GraphQL.Plan Example.Tenant Example.Tenant.Planning
def firstGraph : TenantGraph ⟨[], []⟩ [] [String] := .snoc .nil (.literal .string "first")
def secondGraph : TenantGraph ⟨[], []⟩ [] [String] := .snoc .nil (.literal .string "second")
def firstOutput : OutputRef firstGraph String := ⟨.here⟩
def wrong : OutputRef secondGraph String := firstOutput

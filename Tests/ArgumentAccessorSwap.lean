import Example.Tenant.ArgumentProofs
open GraphQL.Plan Example.Tenant
example : NamedArgument ArgumentProofs.pairArguments "left" := ⟨⟨1, by decide⟩, rfl⟩

import Example.Tenant.ArgumentProofs
open GraphQL.Plan Example.Tenant
example : FieldRepresents Binding.demoAst ⟨"pair", .named "String" true, ArgumentProofs.pairArguments⟩
    ⟨"pair", .pair .string .string, .string⟩ ArgumentProofs.pairArguments.reverse := by decide

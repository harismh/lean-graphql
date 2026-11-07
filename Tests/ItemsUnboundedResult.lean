import Example.Tenant.S4Proofs
open GraphQL.Plan
example : ItemsExample.ResultAllowed (.value 1) (.ok ["a", "b"]) := by
  refine ⟨1, rfl, ?_⟩
  decide

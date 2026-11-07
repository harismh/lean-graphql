import Example.Tenant.S4Proofs
open GraphQL.Plan
example : (ItemsExample.specification (.value 1) [Sum.inl "items"] false).Satisfies (.ok none []) := by
  constructor
  · rfl
  · simp

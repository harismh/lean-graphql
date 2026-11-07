import GraphQL.Plan.Input.Coercion
open GraphQL.Plan.InputCoercion
example (defaults : DefaultMeaning fallback supplied effective) : nullDefaultMutation fallback supplied = effective := by
  exact defaulted_complete defaults

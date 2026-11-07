import GraphQL.Plan.Input.NamedBoundary
open GraphQL.Plan GraphQL.Plan.InputCoercion.NamedBoundary
example : CoercionAgreement swappedCoercion := by
  intro environment arguments a b first second
  exact InputCoercion.NamedExample.named_coercion_complete first second

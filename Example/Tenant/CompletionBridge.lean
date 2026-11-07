import Example.Tenant.Response
import GraphQL.Plan.Completion

namespace Example.Tenant.Spec

def toCompletion : Result α → GraphQL.Plan.Completion Error α
  | .ok value errors => .ok value errors
  | .bubble errors => .bubble errors
def fromCompletion : GraphQL.Plan.Completion Error α → Result α
  | .ok value errors => .ok value errors
  | .bubble errors => .bubble errors

theorem completion_roundtrip (result : Result α) : fromCompletion (toCompletion result) = result := by
  cases result <;> rfl
theorem completion_inverse (result : GraphQL.Plan.Completion Error α) :
    toCompletion (fromCompletion result) = result := by cases result <;> rfl
theorem completion_map (f : α → β) (result : Result α) :
    toCompletion (result.map f) = (toCompletion result).map f := by cases result <;> rfl
theorem completion_pair (f : α → β → γ) (a : Result α) (b : Result β) :
    toCompletion (pair f a b) = GraphQL.Plan.Completion.pair f (toCompletion a) (toCompletion b) := by
  cases a <;> cases b <;> rfl
theorem completion_boundary (nullable : Bool) (result : Result Value) :
    toCompletion (boundary nullable result) =
      GraphQL.Plan.Completion.boundary .null nullable (toCompletion result) := by
  cases result <;> cases nullable <;> rfl
theorem completion_collect (items : List (Result Value)) :
    toCompletion (collect items) = GraphQL.Plan.Completion.collect (items.map toCompletion) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [collect, List.map_cons, GraphQL.Plan.Completion.collect, completion_pair, ih]

end Example.Tenant.Spec

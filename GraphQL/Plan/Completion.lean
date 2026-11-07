import Std

namespace GraphQL.Plan

/-- Error-polymorphic completion; applications choose their own closed error algebra. -/
inductive Completion (error : Type) (α : Type) where
  | ok (value : α) (errors : List error)
  | bubble (errors : List error)
  deriving BEq, Repr

def Completion.errors : Completion error α → List error
  | .ok _ errors | .bubble errors => errors
def Completion.map (f : α → β) : Completion error α → Completion error β
  | .ok value errors => .ok (f value) errors
  | .bubble errors => .bubble errors
def Completion.pair (f : α → β → γ) : Completion error α → Completion error β → Completion error γ
  | .ok a ea, .ok b eb => .ok (f a b) (ea ++ eb)
  | a, b => .bubble (a.errors ++ b.errors)
def Completion.boundary (nullValue : α) (nullable : Bool) : Completion error α → Completion error α
  | .ok a es => .ok a es
  | .bubble es => if nullable then .ok nullValue es else .bubble es
def Completion.collect : List (Completion error α) → Completion error (List α)
  | [] => .ok [] []
  | head :: tail => Completion.pair List.cons head (Completion.collect tail)

theorem completion_pair_errors (f : α → β → γ) (a : Completion error α) (b : Completion error β) :
    (Completion.pair f a b).errors = a.errors ++ b.errors := by cases a <;> cases b <;> rfl

end GraphQL.Plan

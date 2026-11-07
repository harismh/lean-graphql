import Example.Tenant.InputSurface

namespace Example.Tenant.InputSurface

/-- Only the query object has an argument-bearing declaration, and its complete
layout is the singleton required ID argument. There are no field defaults. -/
theorem argument_location (declaration : ObjectField object name arguments child)
    (present : arguments ≠ []) :
    object = .query ∧ name = "project" ∧ ∃ key, arguments = [("id", .string key)] := by
  cases declaration with
  | project key => exact ⟨rfl, rfl, key, rfl⟩
  | projects => exact False.elim (present rfl)
  | tasks => exact False.elim (present rfl)
  | taskProject => exact False.elim (present rfl)

theorem no_query_child (declaration : ObjectField object name arguments child) : child ≠ .query := by
  cases declaration <;> intro impossible <;> cases impossible

/-- Counts argument-bearing fields anywhere in a selection. -/
def argumentCount : PSelection → Nat
  | .nil => 0
  | .field _ args children rest => (if args = [] then 0 else 1) + argumentCount children + argumentCount rest

theorem nonquery_no_arguments (valid : ValidPSelection object selection) (nonquery : object ≠ .query) :
    argumentCount selection = 0 := by
  induction valid with
  | nil => rfl
  | leaf declaration unique tail ih => simpa [argumentCount] using ih nonquery
  | object declaration nonempty unique nested tail childIH tailIH =>
    cases declaration with
    | project => exact False.elim (nonquery rfl)
    | projects => exact False.elim (nonquery rfl)
    | tasks => simp [argumentCount, childIH (by decide), tailIH nonquery]
    | taskProject => simp [argumentCount, childIH (by decide), tailIH nonquery]

theorem query_argument_count (valid : ValidPSelection .query selection) :
    argumentCount selection = if "project" ∈ selection.names then 1 else 0 := by
  generalize objectEq : ObjectType.query = object at valid
  induction valid with
  | nil => simp [argumentCount, PSelection.names]
  | leaf declaration unique tail ih => cases objectEq; cases declaration
  | object declaration nonempty unique nested tail childIH tailIH =>
    cases objectEq
    cases declaration with
    | project =>
      simp [argumentCount, PSelection.names, nonquery_no_arguments nested (by decide), tailIH rfl, unique]
    | projects =>
      simp [argumentCount, PSelection.names, nonquery_no_arguments nested (by decide), tailIH rfl]

theorem at_most_one_argument (valid : ValidOperation operation) :
    argumentCount (skeleton operation.selection) ≤ 1 := by
  rw [query_argument_count valid.1.2]
  split <;> omega

end Example.Tenant.InputSurface

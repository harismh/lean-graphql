import GraphQL.Plan.ResultSpec

namespace GraphQL.Plan

def completeList (nullable elementsNullable : Bool) (rows : List (Completion error (Option α))) :
    Completion error (Option (List (Option α))) :=
  Completion.boundary none nullable
    ((Completion.collect (rows.map (Completion.boundary none elementsNullable))).map some)

theorem boundary_error_order (nullValue : α) (nullable : Bool) (result : Completion error α) :
    (Completion.boundary nullValue nullable result).errors = result.errors := by
  cases result <;> cases nullable <;> rfl

theorem map_error_order (f : α → β) (result : Completion error α) :
    (result.map f).errors = result.errors := by cases result <;> rfl

theorem collect_error_order (rows : List (Completion error α)) :
    (Completion.collect rows).errors = rows.flatMap Completion.errors := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [Completion.collect, completion_pair_errors, List.flatMap_cons, ih]

/-- Errors retain order, paths and multiplicity through all four nullability combinations. -/
theorem list_completion_error_order (nullable elementsNullable : Bool)
    (rows : List (Completion error (Option α))) :
    (completeList nullable elementsNullable rows).errors = rows.flatMap Completion.errors := by
  simp only [completeList, boundary_error_order, map_error_order, collect_error_order, List.flatMap_map]

def elementSpec (P : α → Prop) (E : error → Prop) (nullable : Bool) : ResultSpec error (Option α) :=
  ⟨fun value => match value with | none => nullable = true | some a => P a, E⟩

def listSpec (P : α → Prop) (E : error → Prop) (limit : Nat) (nullable elementsNullable : Bool) :
    ResultSpec error (Option (List (Option α))) :=
  ⟨fun value => match value with
    | none => nullable = true
    | some rows => rows.length ≤ limit ∧ ∀ row ∈ rows, (elementSpec P E elementsNullable).valueValid row, E⟩

theorem list_completion_contract (P : α → Prop) (E : error → Prop) (limit : Nat)
    (nullable elementsNullable : Bool) (rows : List (Completion error (Option α)))
    (bound : rows.length ≤ limit)
    (valid : ∀ row ∈ rows, (elementSpec P E elementsNullable).Satisfies row) :
    (listSpec P E limit nullable elementsNullable).Satisfies (completeList nullable elementsNullable rows) := by
  apply result_boundary
  · exact fun h => h
  · apply result_map (ResultSpec.mk (fun values : List (Option α) =>
        values.length ≤ limit ∧ ∀ value ∈ values, (elementSpec P E elementsNullable).valueValid value) E) _ some
    · exact fun _ h => h
    · exact fun _ h => h
    · apply result_collect_bound (elementSpec P E elementsNullable)
      · simpa using bound
      · intro result member
        obtain ⟨row, included, rfl⟩ := List.mem_map.mp member
        apply result_boundary
        · exact fun h => h
        · exact valid row included

theorem collect_success (values : List α) :
    Completion.collect (values.map (fun value => (Completion.ok value [] : Completion error α))) = .ok values [] := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.map_cons, Completion.collect, ih, Completion.pair, List.nil_append]

theorem list_completion_success (values : List α) (nullable elementsNullable : Bool) :
    completeList (error := error) nullable elementsNullable
      (values.map (fun value => Completion.ok (some value) [])) = .ok (some (values.map some)) [] := by
  simp only [completeList, List.map_map, Function.comp_def, Completion.boundary]
  have rows : (values.map (fun value => (Completion.ok (some value) [] : Completion error (Option α)))) =
      (values.map some).map (fun value => Completion.ok value []) := by simp [List.map_map]
  rw [rows, collect_success]
  rfl

theorem nullable_sibling_survives (left : α) (error : error) :
    Completion.pair Prod.mk (.ok left [])
      (Completion.boundary (none : Option β) true (.bubble [error])) =
      .ok (left, none) [error] := rfl

theorem required_error_stays_error (error : error) :
    Completion.boundary (none : Option α) false (.bubble [error]) = .bubble [error] := rfl

end GraphQL.Plan

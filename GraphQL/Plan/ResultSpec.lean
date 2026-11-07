import GraphQL.Plan.Completion

namespace GraphQL.Plan

/-- Independently chosen predicates; completion requires explicit preservation laws. -/
structure ResultSpec (error value : Type) where
  valueValid : value → Prop
  errorValid : error → Prop

def ResultSpec.Satisfies (spec : ResultSpec error value) : Completion error value → Prop
  | .ok value errors => spec.valueValid value ∧ ∀ error ∈ errors, spec.errorValid error
  | .bubble errors => errors ≠ [] ∧ ∀ error ∈ errors, spec.errorValid error

theorem result_leaf (spec : ResultSpec error value) (value : value) (valid : spec.valueValid value) :
    spec.Satisfies (.ok value []) := ⟨valid, by simp⟩

theorem result_failure (spec : ResultSpec error value) (error : error) (valid : spec.errorValid error) :
    spec.Satisfies (.bubble [error]) := ⟨by simp, by simpa using valid⟩

theorem result_map (left : ResultSpec error α) (right : ResultSpec error β) (f : α → β)
    (values : ∀ value, left.valueValid value → right.valueValid (f value))
    (errors : ∀ error, left.errorValid error → right.errorValid error)
    (result : Completion error α) (valid : left.Satisfies result) :
    right.Satisfies (result.map f) := by
  cases result with
  | ok value es => exact ⟨values value valid.1, fun e he => errors e (valid.2 e he)⟩
  | bubble es => exact ⟨valid.1, fun e he => errors e (valid.2 e he)⟩

theorem result_boundary (spec : ResultSpec error α) (nullValue : α) (nullable : Bool)
    (nullValid : nullable = true → spec.valueValid nullValue)
    (result : Completion error α) (valid : spec.Satisfies result) :
    spec.Satisfies (Completion.boundary nullValue nullable result) := by
  cases result with
  | ok value errors => exact valid
  | bubble errors => cases nullable with
    | false => exact valid
    | true => exact ⟨nullValid rfl, valid.2⟩

theorem result_pair (left : ResultSpec error α) (right : ResultSpec error β) (out : ResultSpec error γ)
    (f : α → β → γ) (values : ∀ a b, left.valueValid a → right.valueValid b → out.valueValid (f a b))
    (leftErrors : ∀ e, left.errorValid e → out.errorValid e)
    (rightErrors : ∀ e, right.errorValid e → out.errorValid e)
    (a : Completion error α) (b : Completion error β) (ha : left.Satisfies a) (hb : right.Satisfies b) :
    out.Satisfies (Completion.pair f a b) := by
  have appendErrors : ∀ (ea eb : List error),
      (∀ e ∈ ea, left.errorValid e) → (∀ e ∈ eb, right.errorValid e) →
      ∀ e ∈ ea ++ eb, out.errorValid e := by
    intro ea eb la rb e he
    cases List.mem_append.mp he with
    | inl hl => exact leftErrors e (la e hl)
    | inr hr => exact rightErrors e (rb e hr)
  cases a <;> cases b <;> constructor
  · exact values _ _ ha.1 hb.1
  · exact appendErrors _ _ ha.2 hb.2
  · simp_all [Completion.pair, ResultSpec.Satisfies, Completion.errors]
  · exact appendErrors _ _ ha.2 hb.2
  · simp_all [Completion.pair, ResultSpec.Satisfies, Completion.errors]
  · exact appendErrors _ _ ha.2 hb.2
  · simp_all [Completion.pair, ResultSpec.Satisfies, Completion.errors]
  · exact appendErrors _ _ ha.2 hb.2

def ResultSpec.list (spec : ResultSpec error α) : ResultSpec error (List α) :=
  ⟨fun values => ∀ value ∈ values, spec.valueValid value, spec.errorValid⟩

theorem result_collect (spec : ResultSpec error α) (rows : List (Completion error α))
    (valid : ∀ row ∈ rows, spec.Satisfies row) : spec.list.Satisfies (Completion.collect rows) := by
  induction rows with
  | nil => exact ⟨by simp [ResultSpec.list], by simp⟩
  | cons head tail ih =>
    apply result_pair spec spec.list spec.list List.cons
    · intro a b ha hb value member
      cases List.mem_cons.mp member with
      | inl eq => subst value; exact ha
      | inr ht => exact hb value ht
    · exact fun _ h => h
    · exact fun _ h => h
    · exact valid head List.mem_cons_self
    · exact ih (fun row member => valid row (List.mem_cons_of_mem _ member))

theorem collect_length (rows : List (Completion error α)) (items : List α) (errors : List error)
    (success : Completion.collect rows = .ok items errors) : items.length = rows.length := by
  induction rows generalizing items errors with
  | nil => cases success; rfl
  | cons head tail ih =>
    cases head <;> cases ht : Completion.collect tail <;>
      simp_all [Completion.collect, Completion.pair, Completion.errors]
    rw [← success.1]
    simp [ih]

theorem result_collect_bound (spec : ResultSpec error α) (rows : List (Completion error α))
    (limit : Nat) (bound : rows.length ≤ limit) (valid : ∀ row ∈ rows, spec.Satisfies row) :
    (ResultSpec.mk (fun values => values.length ≤ limit ∧ ∀ value ∈ values, spec.valueValid value)
      spec.errorValid).Satisfies (Completion.collect rows) := by
  have good := result_collect spec rows valid
  cases h : Completion.collect rows with
  | bubble errors => rw [h] at good; exact good
  | ok values errors =>
    rw [h] at good
    exact ⟨⟨by rw [collect_length rows values errors h]; exact bound, good.1⟩, good.2⟩

end GraphQL.Plan

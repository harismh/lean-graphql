import GraphQL.Plan.Schema

namespace GraphQL.Plan

variable {n : Nat} {source target : Fin n → Type}

/-- Maps only object carriers; scalars, wrappers, list order and public errors remain explicit. -/
def OutputType.mapModels {source target : Fin n → Type} (convert : ∀ o, source o → target o) :
    (shape : OutputType n) → shape.denote source → shape.denote target
  | .string, value => value
  | .int, value => value
  | .boolean, value => value
  | .object owner, value => convert owner value
  | .nullable shape, value => value.map (shape.mapModels convert)
  | .list shape, value => value.map (shape.mapModels convert)

theorem map_models_identity (shape : OutputType n) (value : shape.denote models) :
    shape.mapModels (fun _ x => x) value = value := by
  induction shape with
  | string | int | boolean | object => rfl
  | nullable shape ih => cases value <;> simp [OutputType.mapModels, ih] <;> rfl
  | list shape ih => simp [OutputType.mapModels, show shape.mapModels (fun _ x => x) = id from funext ih] <;> rfl

def convertOutcome (shape : OutputType n) (convert : ∀ o, source o → target o)
    (result : Outcome app (shape.denote source)) : Outcome app (shape.denote target) :=
  result.map (shape.mapModels convert)

theorem convert_outcome_success (shape : OutputType n) (convert : ∀ o, source o → target o)
    (value : shape.denote source) :
    convertOutcome (app := app) shape convert (.ok value) = .ok (shape.mapModels convert value) := rfl

theorem convert_outcome_error (shape : OutputType n) (convert : ∀ o, source o → target o)
    (error : PublicError app) : convertOutcome shape convert (.error error) = .error error := rfl

theorem convert_outcome_identity (shape : OutputType n) (value : Outcome app (shape.denote models)) :
    convertOutcome shape (fun _ value => value) value = value := by
  cases value <;> simp [convertOutcome, Except.map, map_models_identity]

end GraphQL.Plan

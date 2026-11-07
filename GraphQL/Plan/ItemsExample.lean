import GraphQL.Plan.Interpreter
import GraphQL.Plan.ResultSpec
import GraphQL.Plan.ListCompletion

namespace GraphQL.Plan.ItemsExample

inductive Error where
  | badLimit
  deriving DecidableEq, Repr

abbrev schema : Schema := ⟨1, fun _ => [⟨"items", .optional .int, .list .string⟩]⟩
abbrev models : Fin 1 → Type := fun _ => Unit
def field : FieldId schema 0 := ⟨⟨0, by decide⟩⟩

def limit : Input Int → Except Error Nat
  | .omitted | .null => .ok 20
  | .value n => if n < 0 then .error .badLimit else .ok (min n.toNat 100)

def ResultAllowed (args : Input Int) : Outcome Error (List String) → Prop
  | .ok rows => ∃ bound, limit args = .ok bound ∧ rows.length ≤ bound
  | .error (.application error) => limit args = .error error
  | .error (.framework _) => True

def contracts : Contracts schema models (List String) Error where
  pre := fun {_} _ _ _ _ => True
  post := fun {_} f _ _ => match f with
    | ⟨⟨0, _⟩⟩ => ResultAllowed
    | ⟨⟨n + 1, h⟩⟩ => False.elim (by simp [schema] at h)
  compatible := fun {_} _ _ {_} _ => True

def backend : Meanings schema models (List String) Error :=
  fun {_} f rows _ => match f with
  | ⟨⟨0, _⟩⟩ => fun args => match limit args with
    | .ok bound => .ok (rows.take bound)
    | .error code => .error (.application code)
  | ⟨⟨n + 1, h⟩⟩ => False.elim (by simp [schema] at h)

theorem take_backend_contract : BackendSatisfies contracts backend := by
  intro object f rows parent args _
  rcases f with ⟨⟨index, valid⟩⟩
  have eq : index = 0 := by simp [schema] at valid; omega
  subst index
  change ResultAllowed args (match limit args with | .ok bound => .ok (rows.take bound) | .error code => .error (.application code))
  cases found : limit args with
  | ok bound => exact ⟨bound, found, by simp [List.length_take]; omega⟩
  | error code => exact found

def plan : Graph schema models (List String) Error [Unit, List String, Input Int]
    [Outcome Error (List String), Unit, List String, Input Int] :=
  .snoc .nil (.call field (.there .here) .here (.there (.there .here)))

theorem plan_certificate (rows : List String) (args : Input Int) :
    GraphProof contracts plan (fun values => values = ((), rows, args, ()))
      (fun values => ResultAllowed args values.1) := by
  apply GraphProof.snoc (.nil (fun _ h => h))
    (NodeProof.call (fun _ _ => True.intro) (fun _ _ _ h => h))
  intro values eq result valid
  subst values
  exact valid

abbrev Path := List (Sum String Nat)
abbrev LocatedError := PublicError Error × Path

def complete (path : Path) : Outcome Error (List String) → Completion LocatedError (Option (List String))
  | .ok rows => (completeList false false (rows.map (fun row => Completion.ok (some row) []))).map
      (fun value => value.map (List.filterMap id))
  | .error code => .bubble [(code, path)]

theorem complete_success (rows : List String) (path : Path) : complete path (.ok rows) = .ok (some rows) [] := by
  simp only [complete, list_completion_success, Completion.map, Option.map_some]
  congr 2
  simp [List.filterMap_map]

def specification (args : Input Int) (path : Path) (nullable : Bool) : ResultSpec LocatedError (Option (List String)) where
  valueValid := fun value => match value with
    | none => nullable = true
    | some rows => ∃ bound, limit args = .ok bound ∧ rows.length ≤ bound
  errorValid := fun (code, errorPath) => errorPath = path ∧ match code with
    | .application error => limit args = .error error
    | .framework _ => True

theorem complete_contract (args : Input Int) (path : Path) (nullable : Bool)
    (raw : Outcome Error (List String)) (valid : ResultAllowed args raw) :
    (specification args path nullable).Satisfies (Completion.boundary none nullable (complete path raw)) := by
  apply result_boundary
  · exact fun h => h
  · cases raw with
    | ok rows => rw [complete_success]; exact ⟨valid, by simp⟩
    | error code =>
      apply result_failure
      cases code with
      | application error => exact ⟨rfl, valid⟩
      | framework error => exact ⟨rfl, True.intro⟩

/-- This is the executable plan path; arbitrary permitted answers, not backend
normalization, establish the length bound and selected error path. -/
def execute (rows : List String) (args : Input Int) (path : Path) (nullable : Bool := false) :
    Execution schema models (List String) Error (Completion LocatedError (Option (List String))) :=
  (interpretGraph plan ((), rows, args, ())).bind
    (fun values => .done (Completion.boundary none nullable (complete path values.1)))

theorem run_execution (resolve : (call : Call schema models (List String)) → Answer Error call)
    (rows : List String) (args : Input Int) (path : Path) (nullable : Bool) :
    runMachine resolve (execute rows args path nullable) =
      Completion.boundary none nullable (complete path (resolve (.one field rows () args))) := rfl

theorem execution_contract (rows : List String) (args : Input Int) (path : Path) (nullable : Bool) :
    Sat contracts.Pre contracts.Post (execute rows args path nullable) (specification args path nullable).Satisfies := by
  apply sat_bind _ _ (graph_contract_execution (plan_certificate rows args) _ rfl)
  exact fun values valid => complete_contract args path nullable values.1 valid

theorem permitted_driver_bound (resolve : (call : Call schema models (List String)) → Answer Error call)
    (valid : ∀ call, contracts.Pre call → contracts.Post call (resolve call))
    (rows : List String) (args : Input Int) (path : Path) (nullable : Bool) :
    (specification args path nullable).Satisfies (runMachine resolve (execute rows args path nullable)) :=
  sat_run resolve valid _ (execution_contract rows args path nullable)

theorem default_missing : limit .omitted = .ok 20 := rfl
theorem default_null : limit .null = .ok 20 := rfl
theorem negative_rejected (n : Int) (negative : n < 0) : limit (.value n) = .error .badLimit := by simp [limit, negative]
theorem limit_capped (n : Int) (nonnegative : ¬ n < 0) : limit (.value n) = .ok (min n.toNat 100) := by simp [limit, nonnegative]

end GraphQL.Plan.ItemsExample

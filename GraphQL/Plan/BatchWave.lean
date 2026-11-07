import GraphQL.Plan.Batch

namespace GraphQL.Plan.Batch
open GraphQL.Plan
variable {schema : Schema} {models : Fin schema.objectCount → Type} {scope app : Type}

/-- Driver dispatches the certified backend capability, with a pointwise fallback
only for fields not selected by this optimization. -/
def driver (adapter : Adapter schema models scope app) : (call : Call schema models scope) → Answer app call
  | .one field context parent args => (adapter field).single context parent args
  | .batch field context inputs => match (adapter field).batch with
    | some capability => capability.run context inputs
    | none => inputs.map (fun input => (adapter field).single context input.1 input.2)

theorem driver_exact (adapter : Adapter schema models scope app) (call : Call schema models scope) :
    driver adapter call = denoteCall adapter.meanings call := by
  cases call with
  | one => rfl
  | batch field context inputs =>
    simp only [driver]
    split
    · rename_i capability present
      apply Vector.ext
      intro i bound
      exact (capability.exact context inputs ⟨i, bound⟩).trans
        (batch_position adapter.meanings field context inputs ⟨i, bound⟩).symm
    · rfl

theorem run_driver (adapter : Adapter schema models scope app) (machine : Execution schema models scope app α) :
    runMachine (driver adapter) machine = runMachine (denoteCall adapter.meanings) machine := by
  have same : driver adapter = denoteCall adapter.meanings := funext (driver_exact adapter)
  rw [same]

/-- The capability and key witness are tied to this exact field backend. -/
structure Eligible (adapter : Adapter schema models scope app) (field : FieldId schema owner) where
  capability : BatchCapability field (adapter field).single
  present : (adapter field).batch = some capability
  key : SufficientKey field (adapter field).single
  keyed : capability.deduplication = some key

variable {owner : Fin schema.objectCount} {field : FieldId schema owner}
  {adapter : Adapter schema models scope app}

def wave (eligible : Eligible adapter field) (context : scope)
    (rows : List (models owner × field.Args)) (capacity : Nat) (positive : 0 < capacity) :
    Execution schema models scope app (Fin rows.length → Outcome app (field.Out models)) := by
  letI := eligible.key.equal
  let key := fun input : models owner × field.Args => eligible.key.key context input.1 input.2
  exact (load field context (Vector.ofFn (representative key rows)) capacity positive).bind
    (fun answers => .done (fun i => answers (position key rows i)))

def uniqueCount (eligible : Eligible adapter field) (context : scope)
    (rows : List (models owner × field.Args)) : Nat := by
  letI := eligible.key.equal
  exact (keys (fun input => eligible.key.key context input.1 input.2) rows).length

theorem wave_calls (eligible : Eligible adapter field) (context : scope)
    (rows : List (models owner × field.Args)) (positive : 0 < capacity) :
    Calls (wave eligible context rows capacity positive) (chunks (uniqueCount eligible context rows) capacity) := by
  unfold wave uniqueCount
  apply calls_bind (m := 0)
  · exact load_calls _ _ _ positive
  · intro _; rfl

theorem wave_exact (eligible : Eligible adapter field) (context : scope)
    (rows : List (models owner × field.Args)) (positive : 0 < capacity) :
    runMachine (driver adapter) (wave eligible context rows capacity positive) =
      fun i => (adapter field).single context rows[i].1 rows[i].2 := by
  letI := eligible.key.equal
  unfold wave
  rw [run_bind, load_exact field context _ positive (driver adapter)
    ((adapter field).single context) (fun n inputs i => by
      rw [driver_exact]; exact batch_position adapter.meanings field context inputs i)]
  funext i
  have ofFn_get {α : Type} {n : Nat} (f : Fin n → α) (j : Fin n) :
      (Vector.ofFn f).get j = f j := by simp [Vector.get, Fin.cast]
  simp only [runMachine, ofFn_get]
  exact representative_outcome (fun input : models owner × field.Args => eligible.key.key context input.1 input.2)
    (fun input => (adapter field).single context input.1 input.2)
    (fun left right equal => eligible.key.sufficient context left.1 left.2 right.1 right.2 equal) rows i

theorem wave_bound (eligible : Eligible adapter field) (context : scope)
    (rows : List (models owner × field.Args)) (positive : 0 < capacity)
    (resolve : (call : Call schema models scope) → Answer app call) :
    (runCount resolve (wave eligible context rows capacity positive)).2 =
      (uniqueCount eligible context rows + capacity - 1) / capacity :=
  (calls_count _ (wave_calls eligible context rows positive) resolve).trans (chunks_ceiling _ _ positive)

theorem wave_bounded (eligible : Eligible adapter field) (context : scope)
    (rows : List (models owner × field.Args)) (positive : 0 < capacity) :
    Sat (BoundedBatch capacity) (fun _ (_ : Answer app _) => True)
      (wave eligible context rows capacity positive) (fun _ => True) := by
  unfold wave
  apply sat_bind _ _ (load_bounded _ _ _ positive)
  intro _ _; trivial

end GraphQL.Plan.Batch

import GraphQL.Plan.BatchWave

namespace GraphQL.Plan.Batch
open GraphQL.Plan
variable {schema : Schema} {models : Fin schema.objectCount → Type} {scope app : Type}

variable {owner : Fin schema.objectCount} {field : FieldId schema owner}
  {adapter : Adapter schema models scope app}

def rowPosition (rows : Gathered α) (index : RowIndex rows.width) : Fin rows.positions.length :=
  ⟨rows.positions.idxOf index, List.idxOf_lt_length_of_mem (position_present rows index)⟩

def rowInputs (rows : Gathered α) := rows.positions.map rows.getValue

def scatterResults (rows : Gathered α) (results : Fin rows.positions.length → β) :
    RowIndex rows.width → β := fun index => results (rowPosition rows index)

theorem scatter_results_exact (rows : Gathered α) (f : α → β) :
    scatterResults rows (fun i => f (rows.getValue rows.positions[i])) = fun index => f (rows.getValue index) := by
  funext index
  simp [scatterResults, rowPosition]

def rowsWave (eligible : Eligible adapter field) (context : scope)
    (rows : Gathered (models owner × field.Args)) (capacity : Nat) (positive : 0 < capacity) :
    Execution schema models scope app (RowIndex rows.width → Outcome app (field.Out models)) :=
  (wave eligible context (rowInputs rows) capacity positive).bind (fun values =>
    .done (fun index => values ⟨(rowPosition rows index).val, by simpa [rowInputs] using (rowPosition rows index).isLt⟩))

theorem rows_wave_exact (eligible : Eligible adapter field) (context : scope)
    (rows : Gathered (models owner × field.Args)) (positive : 0 < capacity) :
    runMachine (driver adapter) (rowsWave eligible context rows capacity positive) =
      fun index => (adapter field).single context (rows.getValue index).1 (rows.getValue index).2 := by
  simp only [rowsWave, run_bind, wave_exact, runMachine]
  funext index
  simp [rowInputs, rowPosition]

theorem rows_wave_calls (eligible : Eligible adapter field) (context : scope)
    (rows : Gathered (models owner × field.Args)) (positive : 0 < capacity) :
    Calls (rowsWave eligible context rows capacity positive)
      (chunks (uniqueCount eligible context (rowInputs rows)) capacity) := by
  unfold rowsWave
  apply calls_bind (m := 0)
  · exact wave_calls _ _ _ positive
  · intro _; rfl

theorem rows_wave_bounded (eligible : Eligible adapter field) (context : scope)
    (rows : Gathered (models owner × field.Args)) (positive : 0 < capacity) :
    Sat (BoundedBatch capacity) (fun _ (_ : Answer app _) => True)
      (rowsWave eligible context rows capacity positive) (fun _ => True) := by
  unfold rowsWave
  apply sat_bind _ _ (wave_bounded _ _ _ positive)
  intro _ _; trivial

end GraphQL.Plan.Batch

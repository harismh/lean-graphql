import Example.Tenant.BatchExecution

namespace Example.Tenant.Batching
open GraphQL GraphQL.Plan Planning
variable {adapter : Actual}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sequential_calls (request : Binding.Request) (prepared : Prepared) :
    Batch.Calls (sequential request prepared) (rows prepared).positions.length := by
  have inner : ∀ parent, Batch.Calls
      (tabulate (fun task : Fin ((rows prepared).width parent) =>
        invoke (branchId .taskProject) request ((rows prepared).getValue ⟨parent, task⟩).1 ()))
      ((rows prepared).width parent) := fun _ => Batch.tabulate_calls _ (fun _ => ⟨0, rfl, fun _ => rfl⟩)
  have proof := Batch.calls_bind _ (fun values => Machine.done (fun index : RowIndex (rows prepared).width => values index.1 index.2))
    (Batch.tabulate_cost _ (rows prepared).width inner) (fun _ => (rfl : Batch.Calls (.done _) 0))
  simpa [sequential, Gathered.positions, List.length_flatMap, List.finRange, List.map_ofFn, Function.comp_def] using proof

theorem optimized_stage_count (batch : Batch.Eligible adapter (branchId .taskProject))
    (request : Binding.Request) (prepared : Prepared) (positive : 0 < capacity)
    (resolve : (call : Call schema Binding.carriers Binding.Request) → Answer ApplicationError call) :
    (Batch.runCount resolve (Batch.rowsWave batch request (rows prepared) capacity positive)).2 =
      (Batch.uniqueCount batch request (Batch.rowInputs (rows prepared)) + capacity - 1) / capacity :=
  (Batch.calls_count _ (Batch.rows_wave_calls batch request (rows prepared) positive) resolve).trans
    (Batch.chunks_ceiling _ _ positive)

/-- Every staged row was already filtered by the domain resolver. This is the
Task.project parent precondition, before representatives are chosen. -/
theorem prepared_rows_owned (request : Binding.Request)
    (index : RowIndex (rows (preparedFor (Generated.adapter Generated.application) request)).width) :
    OwnedTask request.snapshot request.principal
      ((rows (preparedFor (Generated.adapter Generated.application) request)).getValue index).1 := by
  apply projectTasks_owned
  exact List.getElem_mem index.2.isLt

theorem prepared_input_pre (request : Binding.Request) (input : Task × Unit)
    (member : input ∈ Batch.rowInputs (rows (preparedFor (Generated.adapter Generated.application) request))) :
    Contract.tenant.pre (branchId .taskProject) request input.1 input.2 := by
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  subst input
  exact prepared_rows_owned request index

local instance : DecidableEq Binding.taskProjectKey.Key := Binding.taskProjectKey.equal

theorem representative_pre (request : Binding.Request)
    (i : Fin (Batch.keys (fun input : Task × Unit => Binding.taskProjectKey.key request input.1 input.2)
      (Batch.rowInputs (rows (preparedFor (Generated.adapter Generated.application) request)))).length) :
    let input := Batch.representative (fun input : Task × Unit => Binding.taskProjectKey.key request input.1 input.2)
      (Batch.rowInputs (rows (preparedFor (Generated.adapter Generated.application) request))) i
    Contract.tenant.pre (branchId .taskProject) request input.1 input.2 :=
  prepared_input_pre request _ (Batch.representative_mem _ _ i)

theorem task_batch_compatible (request : Binding.Request)
    (inputs : Vector (Task × Unit) n) :
    Contract.tenant.compatible (branchId .taskProject) request inputs := trivial

end Example.Tenant.Batching

import Example.Tenant.S2bProofs
import GraphQL.Plan.BatchRows

namespace Example.Tenant.Batching
open GraphQL GraphQL.Plan Planning

abbrev Exec := Execution schema Binding.carriers Binding.Request ApplicationError
abbrev Actual := Adapter schema Binding.carriers Binding.Request ApplicationError
variable {adapter : Actual}
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def invoke (field : FieldId schema owner) (request : Binding.Request)
    (parent : Binding.carriers owner) (args : field.Args) : Exec (Outcome ApplicationError (field.Out Binding.carriers)) :=
  .pending (.one field request parent args) .done

def selection (nested : PSelection) : PSelection :=
  .field "projects" [] (.field "tasks" [] (.field "project" [] nested .nil) .nil) .nil

def resolved (child : IR.Resolved .project nested) (nonempty : nested ≠ .nil) :
    IR.Resolved .query (selection nested) :=
  .object .projects () none
    (.object .tasks () none (.object .taskProject () none child nonempty .nil (by simp [PSelection.names]))
      (by intro h; cases h) .nil (by simp [PSelection.names]))
    (by intro h; cases h) .nil (by simp [PSelection.names])

def checked (child : IR.Checked .project nested) (nonempty : nested ≠ .nil) :
    IR.Checked .query (selection nested) := ⟨resolved child.val nonempty, rfl, ⟨rfl, ⟨rfl, child.property, trivial⟩, trivial⟩, trivial⟩

/-- Only the exact selected field-chain is eligible. The retained child plan is
compiled normally, and its fetch/output pair stays intact. -/
structure Eligible (adapter : Actual) (selected : IR.Checked .query surface) where
  nested : PSelection
  child : IR.Checked .project nested
  nonempty : nested ≠ .nil
  shape : surface = selection nested
  batch : Batch.Eligible adapter (branchId .taskProject)

structure Prepared where
  projects : Outcome ApplicationError (List Project)
  tasks : Fin (branchRows (carriers := Binding.carriers) .projects projects).length → Outcome ApplicationError (List Task)

def prepare (request : Binding.Request) : Exec Prepared :=
  .pending (.one (branchId .projects) request () ()) (fun projects =>
    (tabulate (fun i : Fin (branchRows (carriers := Binding.carriers) .projects projects).length =>
      invoke (branchId .tasks) request (branchRows .projects projects)[i] ())).bind
        (fun tasks => .done ⟨projects, tasks⟩))

def rows (prepared : Prepared) : Gathered (Task × Unit) :=
  ⟨(branchRows (carriers := Binding.carriers) .projects prepared.projects).length,
    fun i => (branchRows (carriers := Binding.carriers) .tasks (prepared.tasks i)).length,
    fun index => ((branchRows (carriers := Binding.carriers) .tasks (prepared.tasks index.1))[index.2], ())⟩

abbrev Outcomes (prepared : Prepared) := RowIndex (rows prepared).width → Outcome ApplicationError Project

def sequential (request : Binding.Request) (prepared : Prepared) : Exec (Outcomes prepared) :=
  (tabulate (fun i => tabulate (fun j =>
    invoke (branchId .taskProject) request ((rows prepared).getValue ⟨i, j⟩).1 ()))).bind
      (fun values => .done (fun index => values index.1 index.2))

def assemble (field : IR.Branch parent child)
    (raw : Outcome ApplicationError ((branchId field).Out Binding.carriers))
    (values : List (Spec.Result Spec.Value)) (path : Spec.Path) : Spec.Result Spec.Value :=
  appendField field.name (renderBranch field raw values path) (.ok (.object []) [])

def childResult (request : Binding.Request) (child : IR.Resolved .project nested)
    (project : Project) (path : Spec.Path) : Exec (Spec.Result Spec.Value) :=
  (interpretGraph (compileFor Binding.carriers Binding.Request child).graph (project, request, ())).bind
    (fun values => .done (render (compileFor Binding.carriers Binding.Request child).output ⟨values⟩ path))

/-- Reconstruct each original occurrence after shared loading. All paths are derived
from filtered parent/task positions, never from deduplicated keys. -/
def finish (request : Binding.Request) (child : IR.Resolved .project nested)
    (prepared : Prepared) (outcomes : Outcomes prepared) : Exec Spec.Response :=
  (tabulate (fun parent : Fin (rows prepared).count =>
    (tabulate (fun task : Fin ((rows prepared).width parent) =>
      let raw := outcomes ⟨parent, task⟩
      let path : Spec.Path := [.field "projects", .index parent.val, .field "tasks", .index task.val, .field "project"]
      (traverse (fun project => childResult request child project path)
        (branchRows (carriers := Binding.carriers) .taskProject raw)).bind
          (fun children => .done (assemble .taskProject raw children path)))).bind
      (fun tasks => .done (assemble .tasks (prepared.tasks parent) (List.ofFn tasks)
        [.field "projects", .index parent.val, .field "tasks"])))).bind
    (fun projects => .done (Spec.envelope (assemble .projects prepared.projects (List.ofFn projects) [.field "projects"])))

def reference (request : Binding.Request) (child : IR.Resolved .project nested) : Exec Spec.Response :=
  (prepare request).bind (fun prepared => (sequential request prepared).bind (finish request child prepared))

def optimized (batch : Batch.Eligible adapter (branchId .taskProject)) (request : Binding.Request)
    (child : IR.Resolved .project nested) (capacity : Nat) (positive : 0 < capacity) : Exec Spec.Response :=
  (prepare request).bind (fun prepared =>
    (Batch.rowsWave batch request (rows prepared) capacity positive).bind (finish request child prepared))

theorem sequential_exact (adapter : Actual) (request : Binding.Request) (prepared : Prepared) :
    runMachine (Batch.driver adapter) (sequential request prepared) =
      fun index => (adapter (branchId .taskProject)).single request ((rows prepared).getValue index).1 () := by
  simp only [sequential, run_bind, run_tabulate, runMachine, invoke, Batch.driver]

theorem optimized_reference (batch : Batch.Eligible adapter (branchId .taskProject)) (request : Binding.Request)
    (child : IR.Resolved .project nested) (positive : 0 < capacity) :
    runMachine (Batch.driver adapter) (optimized batch request child capacity positive) =
      runMachine (Batch.driver adapter) (reference request child) := by
  simp only [optimized, reference, run_bind]
  let prepared := runMachine (Batch.driver adapter) (prepare request)
  exact congrArg (fun outcomes : Outcomes prepared => runMachine (Batch.driver adapter) (finish request child prepared outcomes))
    ((Batch.rows_wave_exact batch request (rows prepared) positive).trans (sequential_exact adapter request prepared).symm)

theorem child_result_exact (adapter : Actual) (request : Binding.Request)
    (child : IR.Resolved .project nested) (project : Project) (path : Spec.Path) :
    runMachine (Batch.driver adapter) (childResult request child project path) =
      denoteResolved adapter.meanings child project request path := by
  apply (Batch.run_driver adapter (childResult request child project path)).trans
  simp only [childResult, run_bind, interpreter_denotation, runMachine]
  exact compile_for_correct child adapter.meanings project request path

theorem indexed_map (values : List α) (f : α × Nat → β) :
    List.ofFn (fun i : Fin values.length => f (values[i], i.val)) =
      values.zipIdx.map f := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp

theorem map_as_indexed (values : List α) (f : α → β) :
    values.map f = List.ofFn (fun i : Fin values.length => f values[i]) := by
  apply List.ext_getElem
  · simp
  · intro i left right; simp

def preparedFor (adapter : Actual) (request : Binding.Request) : Prepared :=
  ⟨(adapter (branchId .projects)).single request () (), fun i =>
    (adapter (branchId .tasks)).single request
      (branchRows (carriers := Binding.carriers) .projects ((adapter (branchId .projects)).single request () ()))[i] ()⟩

theorem prepare_exact (adapter : Actual) (request : Binding.Request) :
    runMachine (Batch.driver adapter) (prepare request) = preparedFor adapter request := by
  simp only [prepare, runMachine, run_bind, run_tabulate, invoke, Batch.driver, preparedFor]

theorem reference_denotes (adapter : Actual) (request : Binding.Request)
    (child : IR.Resolved .project nested) (nonempty : nested ≠ .nil) :
    runMachine (Batch.driver adapter) (reference request child) =
      Spec.envelope (denoteResolved adapter.meanings (resolved child nonempty) () request []) := by
  unfold reference
  rw [run_bind, prepare_exact, run_bind, sequential_exact]
  simp only [finish, run_bind, run_tabulate, run_traverse, runMachine, child_result_exact]
  simp [resolved, denoteResolved, branchCall, branchRows, branchArgs, Adapter.meanings,
    preparedFor, rows, assemble, IR.Branch.name, childPath, isList]
  dsimp only [branchId, schema, FieldId.decl, InputType.denote, Binding.carriers]
  simp only [← indexed_map]
  simp only [map_as_indexed]
  rfl

end Example.Tenant.Batching

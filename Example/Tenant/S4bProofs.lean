import Example.Tenant.BatchAccounting

namespace Example.Tenant.S4bProofs
open GraphQL.Plan Planning Batching
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

abbrev adapter : Batching.Actual := Generated.adapter Generated.application

def child : IR.Checked .project (.field "title" [] .nil .nil) :=
  ⟨.leaf .projectTitle .nil (by simp [PSelection.names]), by trivial⟩

def selected := Batching.checked child (by intro h; cases h)

def firstTarget : Project := ⟨"shared", 1, "first", []⟩
def secondTarget : Project := ⟨"shared", 1, "second", []⟩
def left : Project := ⟨"left", 1, "left", ["t1", "hidden", "t2", "t3"]⟩
def right : Project := ⟨"right", 1, "right", ["t4", "t5"]⟩
def tasks : List Task := [⟨"t1", 1, "one", "shared"⟩, ⟨"hidden", 2, "secret", "shared"⟩,
  ⟨"t2", 1, "two", "shared"⟩, ⟨"t3", 1, "three", "missing"⟩,
  ⟨"t4", 1, "four", "missing"⟩, ⟨"t5", 1, "five", "private"⟩]
def request : Binding.Request :=
  ⟨⟨[left, right, firstTarget, secondTarget, ⟨"private", 2, "secret", []⟩], tasks⟩, ⟨1⟩⟩
def prepared := Batching.preparedFor adapter request

theorem recognized : (Batching.recognize adapter selected).isSome = true := by decide +kernel

theorem filtered_occurrences : (Batch.rowInputs (Batching.rows prepared)).length = 5 := by decide +kernel

theorem distinct_keys_across_parents : Batch.uniqueCount Batching.generatedCapability request
    (Batch.rowInputs (Batching.rows prepared)) = 3 := by decide +kernel

theorem reference_five_calls :
    (Batch.runCount (Batch.driver adapter) (Batching.sequential request prepared)).2 = 5 := by decide +kernel

theorem optimized_two_calls :
    (Batch.runCount (Batch.driver adapter) (Batch.rowsWave Batching.generatedCapability request
      (Batching.rows prepared) 2 (by decide))).2 = 2 := by decide +kernel

theorem strict_improvement :
    (Batch.runCount (Batch.driver adapter) (Batch.rowsWave Batching.generatedCapability request
      (Batching.rows prepared) 2 (by decide))).2 <
    (Batch.runCount (Batch.driver adapter) (Batching.sequential request prepared)).2 := by decide +kernel

theorem first_owned_duplicate : Binding.taskProjectSingle request ⟨"any", 1, "", "shared"⟩ () =
    .ok firstTarget := rfl

theorem whole_response : runMachine (Batch.driver adapter) (Batching.execute adapter request selected 2 (by decide)) =
    Runtime.run adapter request selected :=
  Batching.execute_eq_runtime adapter Generated.application_agreement request selected (by decide)

def expectedErrors : List Spec.Error := [
  ⟨.application .unavailable, [.field "projects", .index 0, .field "tasks", .index 2, .field "project"]⟩,
  ⟨.application .unavailable, [.field "projects", .index 1, .field "tasks", .index 0, .field "project"]⟩,
  ⟨.application .unavailable, [.field "projects", .index 1, .field "tasks", .index 1, .field "project"]⟩]

theorem per_occurrence_errors :
    (runMachine (Batch.driver adapter) (Batching.execute adapter request selected 2 (by decide))).errors = expectedErrors := by
  rw [whole_response]
  decide +kernel

theorem empty_wave :
    (Batch.runCount (Batch.driver adapter) (Batch.wave Batching.generatedCapability request [] 2 (by decide))).2 = 0 := by decide +kernel

theorem chunk_boundaries : Batch.chunks 0 2 = 0 ∧ Batch.chunks 1 2 = 1 ∧ Batch.chunks 2 2 = 1 ∧
    Batch.chunks 3 2 = 2 ∧ Batch.chunks 4 2 = 2 ∧ Batch.chunks 5 2 = 3 := by decide

def twoRows : Gathered String := gather (Nested.ofLists [["first"], ["second"]])
def wrongScatter (_ : RowIndex twoRows.width) : String := "first"

theorem wrong_scatter_rejected : wrongScatter ≠ twoRows.getValue := by
  intro equal
  have wrong := congrFun equal ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  change "first" = "second" at wrong
  contradiction

def otherRequest : Binding.Request := { request with snapshot := ⟨[secondTarget], []⟩ }
def sharedTask : Task := ⟨"same", 1, "", "shared"⟩

theorem equal_key_across_snapshots : Binding.taskProjectKey.key request sharedTask () =
    Binding.taskProjectKey.key otherRequest sharedTask () := rfl

theorem cross_scope_reuse_rejected : Binding.taskProjectSingle request sharedTask () ≠
    Binding.taskProjectSingle otherRequest sharedTask () := by
  change (Except.ok firstTarget : Outcome ApplicationError Project) ≠ .ok secondTarget
  intro equal
  have wrong := congrArg Project.title (Except.ok.inj equal)
  change "first" = "second" at wrong
  contradiction

theorem excluded_operation : Batching.execute adapter request S1Proofs.success 2 (by decide) =
    Runtime.execute request S1Proofs.success := by rfl

def wrongPositionWave : Batching.Exec (Batching.Outcomes prepared) :=
  (Batch.wave Batching.generatedCapability request (Batch.rowInputs (Batching.rows prepared)) 2 (by decide)).bind
    (fun answers => .done (fun _ => answers ⟨0, by decide⟩))

def successful (outcome : Outcome ApplicationError Project) : Bool :=
  match outcome with | .ok _ => true | .error _ => false

theorem wrong_wave_rejected :
    runMachine (Batch.driver adapter) wrongPositionWave ≠
      runMachine (Batch.driver adapter) (Batch.rowsWave Batching.generatedCapability request
        (Batching.rows prepared) 2 (by decide)) := by
  intro equal
  have wrong := congrFun equal ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩
  have separated : successful (runMachine (Batch.driver adapter) wrongPositionWave ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩) ≠
      successful (runMachine (Batch.driver adapter) (Batch.rowsWave Batching.generatedCapability request
        (Batching.rows prepared) 2 (by decide)) ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩) := by decide +kernel
  exact separated (congrArg successful wrong)

theorem wrong_wave_loses_errors :
    (runMachine (Batch.driver adapter) (wrongPositionWave.bind (Batching.finish request child.val prepared))).errors = [] := by
  decide +kernel

theorem whole_path_counts :
    (Batch.runCount (Batch.driver adapter) (Batching.execute adapter request selected 2 (by decide))).2 = 9 ∧
    (Batch.runCount (Batch.driver adapter) (Runtime.execute request selected)).2 = 12 := by decide +kernel

end Example.Tenant.S4bProofs

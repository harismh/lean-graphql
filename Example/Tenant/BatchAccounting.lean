import Example.Tenant.BatchCost

namespace Example.Tenant.Batching
open GraphQL GraphQL.Plan Planning
variable {adapter : Actual}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Setup and output are measured on the actual emitted programs, including every
single/batch suspension they contain. They are not assumed to have zero cost. -/
def setupCount (adapter : Actual) (request : Binding.Request) : Nat :=
  (Batch.runCount (Batch.driver adapter) (prepare request)).2

def outputCount (adapter : Actual) (request : Binding.Request) (child : IR.Resolved .project nested) : Nat :=
  let prepared := runMachine (Batch.driver adapter) (prepare request)
  let outcomes := runMachine (Batch.driver adapter) (sequential request prepared)
  (Batch.runCount (Batch.driver adapter) (finish request child prepared outcomes)).2

def occurrenceCount (adapter : Actual) (request : Binding.Request) : Nat :=
  (rows (runMachine (Batch.driver adapter) (prepare request))).positions.length

def waveCount (batch : Batch.Eligible adapter (branchId .taskProject)) (request : Binding.Request)
    (capacity : Nat) : Nat :=
  let prepared := runMachine (Batch.driver adapter) (prepare request)
  (Batch.uniqueCount batch request (Batch.rowInputs (rows prepared)) + capacity - 1) / capacity

theorem reference_accounting_any (resolve : (call : Call schema Binding.carriers Binding.Request) → Answer ApplicationError call)
    (request : Binding.Request) (child : IR.Resolved .project nested) :
    let prepared := runMachine resolve (prepare request)
    let outcomes := runMachine resolve (sequential request prepared)
    (Batch.runCount resolve (reference request child)).2 =
      (Batch.runCount resolve (prepare request)).2 + (rows prepared).positions.length +
        (Batch.runCount resolve (finish request child prepared outcomes)).2 := by
  dsimp only
  simp only [reference, Batch.count_bind]
  rw [Batch.calls_count _ (sequential_calls request _) resolve]
  omega

theorem optimized_accounting_any (batch : Batch.Eligible adapter (branchId .taskProject))
    (resolve : (call : Call schema Binding.carriers Binding.Request) → Answer ApplicationError call)
    (request : Binding.Request) (child : IR.Resolved .project nested) (positive : 0 < capacity) :
    let prepared := runMachine resolve (prepare request)
    let outcomes := runMachine resolve (Batch.rowsWave batch request (rows prepared) capacity positive)
    (Batch.runCount resolve (optimized batch request child capacity positive)).2 =
      (Batch.runCount resolve (prepare request)).2 +
        (Batch.uniqueCount batch request (Batch.rowInputs (rows prepared)) + capacity - 1) / capacity +
        (Batch.runCount resolve (finish request child prepared outcomes)).2 := by
  dsimp only
  simp only [optimized, Batch.count_bind]
  rw [optimized_stage_count batch request _ positive resolve]
  omega

theorem reference_total (adapter : Actual) (request : Binding.Request) (child : IR.Resolved .project nested) :
    (Batch.runCount (Batch.driver adapter) (reference request child)).2 =
      setupCount adapter request + occurrenceCount adapter request + outputCount adapter request child := by
  simp only [reference, Batch.count_bind, setupCount, occurrenceCount, outputCount]
  rw [Batch.calls_count _ (sequential_calls request _) (Batch.driver adapter)]
  omega

theorem optimized_total (batch : Batch.Eligible adapter (branchId .taskProject)) (request : Binding.Request)
    (child : IR.Resolved .project nested) (positive : 0 < capacity) :
    (Batch.runCount (Batch.driver adapter) (optimized batch request child capacity positive)).2 =
      setupCount adapter request + waveCount batch request capacity + outputCount adapter request child := by
  simp only [optimized, Batch.count_bind, setupCount, waveCount, outputCount]
  rw [optimized_stage_count batch request _ positive (Batch.driver adapter)]
  have same := (Batch.rows_wave_exact batch request
    (rows (runMachine (Batch.driver adapter) (prepare request))) positive).trans
      (sequential_exact adapter request _).symm
  rw [same]
  simp only [Nat.add_assoc]

theorem total_savings (batch : Batch.Eligible adapter (branchId .taskProject)) (request : Binding.Request)
    (child : IR.Resolved .project nested) (positive : 0 < capacity) :
    (Batch.runCount (Batch.driver adapter) (optimized batch request child capacity positive)).2 +
        occurrenceCount adapter request =
      (Batch.runCount (Batch.driver adapter) (reference request child)).2 + waveCount batch request capacity := by
  rw [optimized_total, reference_total]
  omega

theorem dispatcher_total (adapter : Actual) (request : Binding.Request) (selected : IR.Checked .query surface)
    (positive : 0 < capacity) (eligible : Eligible adapter selected)
    (recognized : recognize adapter selected = some eligible) :
    (Batch.runCount (Batch.driver adapter) (execute adapter request selected capacity positive)).2 =
      setupCount adapter request + waveCount eligible.batch request capacity +
        outputCount adapter request eligible.child.val := by
  simp only [execute, recognized]
  exact optimized_total eligible.batch request eligible.child.val positive

end Example.Tenant.Batching

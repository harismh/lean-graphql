import Example.Tenant.BatchPlan

namespace Example.Tenant.Batching
open GraphQL GraphQL.Plan Planning
variable {adapter : Actual}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem optimized_runtime (batch : Batch.Eligible adapter (branchId .taskProject))
    (request : Binding.Request) (child : IR.Checked .project nested) (nonempty : nested ≠ .nil)
    (positive : 0 < capacity) :
    runMachine (Batch.driver adapter) (optimized batch request child.val capacity positive) =
      Runtime.run adapter request (checked child nonempty) := by
  apply (optimized_reference batch request child.val positive).trans
  apply (reference_denotes adapter request child.val nonempty).trans
  symm
  exact (Runtime.run_eq_plan adapter request (checked child nonempty)).trans
    (congrArg Spec.envelope (compile_for_correct (resolved child.val nonempty) adapter.meanings () request []))

theorem optimized_spec (batch : Batch.Eligible adapter (branchId .taskProject))
    (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (child : IR.Checked .project nested) (nonempty : nested ≠ .nil)
    (positive : 0 < capacity) :
    runMachine (Batch.driver adapter) (optimized batch request child.val capacity positive) =
      Spec.EvalSpec (Spec.tenantMeanings request.snapshot request.principal) (selection nested) :=
  (optimized_runtime batch request child nonempty positive).trans
    (Runtime.run_eq_spec adapter agreement request (checked child nonempty))

def capability? (adapter : Actual) : Option (Batch.Eligible adapter (branchId .taskProject)) :=
  match present : (adapter (branchId .taskProject)).batch with
  | none => none
  | some capability => match keyed : capability.deduplication with
    | none => none
    | some key => some ⟨capability, present, key, keyed⟩

def recognizeShape (adapter : Actual) : (surface : PSelection) →
    (selected : IR.Checked .query surface) → Option (Eligible adapter selected)
  | .field "projects" [] (.field "tasks" [] (.field "project" [] nested .nil) .nil) .nil, _ =>
    match capability? adapter, IR.lower .project nested with
    | some batch, some child =>
      if nonempty : nested ≠ .nil then some ⟨nested, child, nonempty, rfl, batch⟩ else none
    | _, _ => none
  | _, _ => none

def recognize (adapter : Actual) (selected : IR.Checked .query surface) : Option (Eligible adapter selected) :=
  recognizeShape adapter surface selected

/-- The dispatcher changes only the recognized query shape with a present exact,
keyed capability. All excluded operations retain the original Machine verbatim. -/
def execute (adapter : Actual) (request : Binding.Request) (selected : IR.Checked .query surface)
    (capacity : Nat) (positive : 0 < capacity) : Exec Spec.Response :=
  match recognize adapter selected with
  | none => Runtime.execute request selected
  | some eligible => optimized eligible.batch request eligible.child.val capacity positive

theorem excluded_unchanged (adapter : Actual) (request : Binding.Request)
    (selected : IR.Checked .query surface) (positive : 0 < capacity)
    (excluded : recognize adapter selected = none) :
    execute adapter request selected capacity positive = Runtime.execute request selected := by
  simp only [execute, excluded]

theorem execute_eq_runtime_any (adapter : Actual)
    (request : Binding.Request) (selected : IR.Checked .query surface) (positive : 0 < capacity) :
    runMachine (Batch.driver adapter) (execute adapter request selected capacity positive) =
      Runtime.run adapter request selected := by
  unfold execute
  split
  · exact Batch.run_driver adapter (Runtime.execute request selected)
  · rename_i eligible found
    obtain ⟨nested, child, nonempty, shape, batch⟩ := eligible
    cases shape
    apply (optimized_runtime batch request child nonempty positive).trans
    exact congrArg (Runtime.run adapter request) (IR.checked_unique (checked child nonempty) selected)

theorem execute_eq_runtime (adapter : Actual) (_agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query surface) (positive : 0 < capacity) :
    runMachine (Batch.driver adapter) (execute adapter request selected capacity positive) =
      Runtime.run adapter request selected := execute_eq_runtime_any adapter request selected positive

theorem execute_authorized (adapter : Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query surface) (nonempty : surface ≠ .nil)
    (positive : 0 < capacity) :
    Spec.AuthorizedResponse request.snapshot request.principal surface
      (runMachine (Batch.driver adapter) (execute adapter request selected capacity positive)) := by
  rw [execute_eq_runtime adapter agreement]
  exact Runtime.run_authorized adapter agreement request selected nonempty

theorem execute_conforms (adapter : Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query surface) (nonempty : surface ≠ .nil)
    (positive : 0 < capacity) :
    Spec.Conforms surface (runMachine (Batch.driver adapter) (execute adapter request selected capacity positive)) := by
  rw [execute_eq_runtime adapter agreement]
  exact Runtime.run_conforms adapter agreement request selected nonempty

def generatedCapability : Batch.Eligible (Generated.adapter Generated.application) (branchId .taskProject) :=
  ⟨Binding.taskProjectBatch, rfl, Binding.taskProjectKey, rfl⟩

end Example.Tenant.Batching

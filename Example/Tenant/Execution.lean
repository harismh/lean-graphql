import Example.Tenant.OutputEvidence
import GraphQL.Plan.Interpreter

namespace Example.Tenant.Runtime
open GraphQL.Plan Planning

/-- The P1 application entry executes the compiled graph and reconstructs its output.
It uses the same Machine consumed by effect drivers; no fuel or alternate evaluator. -/
def execute (request : Binding.Request) (selected : IR.Checked .query selection) :
    GraphQL.Plan.Execution schema Binding.carriers Binding.Request ApplicationError Spec.Response :=
  (interpretGraph (compileFor Binding.carriers Binding.Request selected.val).graph ((), request, ())).bind
    (fun values => .done (Spec.envelope (render (compileFor Binding.carriers Binding.Request selected.val).output ⟨values⟩ [])))

def run (adapter : ExecutionBridge.ActualAdapter) (request : Binding.Request)
    (selected : IR.Checked .query selection) : Spec.Response :=
  runMachine (denoteCall (Adapter.meanings adapter)) (execute request selected)

theorem run_eq_plan (adapter : ExecutionBridge.ActualAdapter) (request : Binding.Request)
    (selected : IR.Checked .query selection) : run adapter request selected = ExecutionBridge.actualResponse adapter request selected := by
  exact (run_bind (denoteCall (Adapter.meanings adapter)) _ _).trans
    (congrArg (fun values => Spec.envelope (render
      (compileFor Binding.carriers Binding.Request selected.val).output ⟨values⟩ []))
      (interpreter_denotation (compileFor Binding.carriers Binding.Request selected.val).graph
        (Adapter.meanings adapter) ((), request, ())))

theorem run_eq_spec (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter) (request : Binding.Request)
    (selected : IR.Checked .query selection) :
    run adapter request selected = Spec.EvalSpec (Spec.tenantMeanings request.snapshot request.principal) selection :=
  (run_eq_plan adapter request selected).trans (ExecutionBridge.actual_response_eq adapter agreement request selected)

theorem run_authorized (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter) (request : Binding.Request)
    (selected : IR.Checked .query selection) (nonempty : selection ≠ .nil) :
    Spec.AuthorizedResponse request.snapshot request.principal selection (run adapter request selected) := by
  rw [run_eq_plan]
  exact ExecutionBridge.actual_response_authorized adapter agreement request selected nonempty

theorem run_conforms (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter) (request : Binding.Request)
    (selected : IR.Checked .query selection) (nonempty : selection ≠ .nil) :
    Spec.Conforms selection (run adapter request selected) := by
  rw [run_eq_plan]
  exact ExecutionBridge.actual_response_conforms adapter agreement request selected nonempty

/-- The proved manual adapter witnesses consistency of the exact contract with EvalSpec;
the resulting Sat statement is independent of the chosen driver. -/
theorem deterministic_execution_contract (request : Binding.Request) (selected : IR.Checked .query selection) :
    Sat Contract.tenant.Pre Contract.tenant.Post (execute request selected)
      (fun response => response = Spec.EvalSpec (Spec.tenantMeanings request.snapshot request.principal) selection) := by
  apply sat_bind _ _ (graph_contract_execution (Contract.compiled_certificate selected.val () request True.intro) _ rfl)
  intro values exactFrame
  change values = _ at exactFrame
  subst values
  have eq := ExecutionBridge.actual_response_eq (Binding.adapt Binding.application) Binding.application_agreement request selected
  have manual := Contract.compiled_frame_invariant selected.val (Binding.adapt Binding.application)
    Binding.application_agreement () request True.intro
  unfold ExecutionBridge.actualResponse operationDenotes runDenotation at eq
  change _ = _ at manual
  exact (congrArg (fun values => Spec.envelope (render
    (compileFor Binding.carriers Binding.Request selected.val).output ⟨values⟩ [])) manual).symm.trans eq

theorem argument_error_no_call (field : IR.Branch parent child) (code : Example.Tenant.FrameworkError)
    (token : Ref inputs Binding.Request) (row : Ref inputs (Binding.carriers (objectId parent)))
    (args : Ref inputs (branchId field).Args) (values : Values inputs) :
    interpretNode (callNode field (some code) token row args) values =
      (.done (.error (.framework (frameworkCode code))) : GraphQL.Plan.Execution schema Binding.carriers Binding.Request ApplicationError _) := rfl

end Example.Tenant.Runtime

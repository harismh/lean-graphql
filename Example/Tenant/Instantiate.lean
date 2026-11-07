import Example.Tenant.Prepare
import Example.Tenant.S4bProofs

namespace Example.Tenant.Preparation
open GraphQL.Plan GraphQL.Plan.InputCoercion

/-- With a valid operation, absence means there is no root project field: S0
requires its singleton id argument. This placeholder key is then unobserved. -/
def idKey (expression : Option Expr) (environment : Environment) : Except InputCoercion.Error String :=
  match expression with
  | none => .ok ""
  | some expression => match argument ⟨.id, true⟩ none environment (some expression) with
    | .ok (.value key) => .ok key
    | .error error => .error error
    | .ok .omitted | .ok .null => .error .required

def keyValue : Except InputCoercion.Error String → String
  | .ok value => value
  | .error _ => ""

def keyError : Except InputCoercion.Error String → Option FrameworkError
  | .ok _ => none
  | .error _ => some .argument

structure Instance (object : ObjectType) (source : PSelection) (key : Except InputCoercion.Error String) where
  selection : PSelection
  resolved : IR.Resolved object selection
  names : selection.names = source.names
  clean : keyError key = none → IR.Clean resolved

theorem instantiated_nonempty (built : Instance object source key) (nonempty : source ≠ .nil) : built.selection ≠ .nil := by
  intro empty
  have names := built.names
  rw [empty] at names
  cases source with
  | nil => exact nonempty rfl
  | field => simp [PSelection.names] at names

def instantiate (key : Except InputCoercion.Error String) :
    (source : IR.Resolved object surface) → IR.Clean source → Instance object surface key
  | .nil, _ => ⟨.nil, .nil, rfl, fun _ => trivial⟩
  | .leaf field rest fresh, clean =>
    let tail := instantiate key rest clean
    ⟨_, .leaf field tail.resolved (by rw [tail.names]; exact fresh),
      by simp only [PSelection.names, tail.names], by intro success; exact tail.clean success⟩
  | .object .project args _ children nonempty rest fresh, clean =>
    let nested := instantiate key children clean.2.1
    let tail := instantiate key rest clean.2.2
    ⟨_, .object .project (keyValue key) (keyError key) nested.resolved (instantiated_nonempty nested nonempty)
      tail.resolved (by rw [tail.names]; exact fresh),
      by simp only [PSelection.names, IR.Branch.name, tail.names],
      by intro success; exact ⟨success, nested.clean success, tail.clean success⟩⟩
  | .object .projects args _ children nonempty rest fresh, clean =>
    let nested := instantiate key children clean.2.1
    let tail := instantiate key rest clean.2.2
    ⟨_, .object .projects args none nested.resolved (instantiated_nonempty nested nonempty)
      tail.resolved (by rw [tail.names]; exact fresh),
      by simp only [PSelection.names, IR.Branch.name, tail.names],
      by intro success; exact ⟨rfl, nested.clean success, tail.clean success⟩⟩
  | .object .tasks args _ children nonempty rest fresh, clean =>
    let nested := instantiate key children clean.2.1
    let tail := instantiate key rest clean.2.2
    ⟨_, .object .tasks args none nested.resolved (instantiated_nonempty nested nonempty)
      tail.resolved (by rw [tail.names]; exact fresh),
      by simp only [PSelection.names, IR.Branch.name, tail.names],
      by intro success; exact ⟨rfl, nested.clean success, tail.clean success⟩⟩
  | .object .taskProject args _ children nonempty rest fresh, clean =>
    let nested := instantiate key children clean.2.1
    let tail := instantiate key rest clean.2.2
    ⟨_, .object .taskProject args none nested.resolved (instantiated_nonempty nested nonempty)
      tail.resolved (by rw [tail.names]; exact fresh),
      by simp only [PSelection.names, IR.Branch.name, tail.names],
      by intro success; exact ⟨rfl, nested.clean success, tail.clean success⟩⟩

/-- S4's actual graph interpreter and output plan, also permitting proved field
argument-error nodes. The clean entry is definitionally the old Runtime.execute. -/
def executeResolved (request : Binding.Request) (resolved : IR.Resolved .query selection) : Batching.Exec Spec.Response :=
  (interpretGraph (Planning.compileFor Binding.carriers Binding.Request resolved).graph ((), request, ())).bind
    (fun values => .done (Spec.envelope (Planning.render
      (Planning.compileFor Binding.carriers Binding.Request resolved).output ⟨values⟩ [])))

theorem execute_clean (request : Binding.Request) (selected : IR.Checked .query selection) :
    executeResolved request selected.val = Runtime.execute request selected := rfl

theorem resolved_run (adapter : Batching.Actual) (request : Binding.Request) (resolved : IR.Resolved .query selection) :
    runMachine (Batch.driver adapter) (executeResolved request resolved) =
      Spec.envelope (Planning.denoteResolved adapter.meanings resolved () request []) := by
  apply (Batch.run_driver adapter (executeResolved request resolved)).trans
  simp only [executeResolved, run_bind, interpreter_denotation, runMachine]
  exact congrArg Spec.envelope (Planning.compile_for_correct resolved adapter.meanings () request [])

theorem resolved_authorized (request : Binding.Request) (resolved : IR.Resolved .query selection)
    (nonempty : selection ≠ .nil) :
    Sat Fault.contracts.Pre Fault.contracts.Post (executeResolved request resolved)
      (Spec.AuthorizedResponse request.snapshot request.principal selection) := by
  apply sat_bind _ _ (Fault.compiled_fault_contract resolved request () True.intro)
  intro values evidence
  obtain ⟨tree, authorized, erased⟩ := evidence.2 []
  exact ⟨⟨nonempty, IR.resolved_valid resolved⟩, tree, authorized, congrArg Spec.envelope erased⟩

end Example.Tenant.Preparation

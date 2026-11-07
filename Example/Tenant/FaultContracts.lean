import Example.Tenant.Execution

namespace Example.Tenant.Fault
open GraphQL.Plan Planning

/-- Success remains exact. A declared framework failure may replace any resolver outcome. -/
def Post (field : FieldId schema object) (request : Binding.Request)
    (parent : Binding.carriers object) (args : field.Args) (outcome : Outcome ApplicationError (field.Out Binding.carriers)) : Prop :=
  Contract.tenant.post field request parent args outcome ∨
    ∃ code : GraphQL.Plan.FrameworkError, outcome = .error (.framework code)

def contracts : Contracts schema Binding.carriers Binding.Request ApplicationError where
  pre := Contract.tenant.pre
  post := Post
  compatible := fun {_} _ _ {_} _ => True

theorem exact_or_fault (field : FieldId schema object) (request : Binding.Request)
    (parent : Binding.carriers object) (args : field.Args)
    (outcome : Outcome ApplicationError (field.Out Binding.carriers))
    (valid : Post field request parent args outcome) :
    outcome = Contract.Expected field request parent args ∨
      ∃ code : GraphQL.Plan.FrameworkError, outcome = .error (.framework code) :=
  valid.elim (fun h => Or.inl h.1) Or.inr

def FrameEvidence (resolved : IR.Resolved object selection) (request : Binding.Request)
    (source : Model request.snapshot object)
    (values : Values (compileFor Binding.carriers Binding.Request resolved).outputs) : Prop :=
  (compileFor Binding.carriers Binding.Request resolved).graph.inputs.project values =
    (Binding.transport request.snapshot (objectId object) source, request, ()) ∧
  ∀ path, ∃ tree, Spec.AuthTree request.snapshot request.principal (context request.snapshot object source)
    selection path tree ∧ Spec.erase tree = render (compileFor Binding.carriers Binding.Request resolved).output ⟨values⟩ path

def ChildEvidence (resolved : IR.Resolved object selection) (request : Binding.Request)
    (source : Model request.snapshot object) (values : Values (compileFor Binding.carriers Binding.Request resolved).outputs) : Prop :=
  ∀ path, ∃ tree, Spec.AuthTree request.snapshot request.principal (context request.snapshot object source)
    selection path tree ∧ Spec.erase tree = render (compileFor Binding.carriers Binding.Request resolved).output ⟨values⟩ path

theorem leaf_evidence (field : IR.Leaf object) (request : Binding.Request)
    (source : Model request.snapshot object)
    (owned : Spec.OwnedContext request.principal (context request.snapshot object source))
    (outcome : Outcome ApplicationError ((leafId field).Out Binding.carriers))
    (valid : Post (leafId field) request (Binding.transport request.snapshot (objectId object) source) (leafArgs field) outcome)
    (path : Spec.Path) :
    ∃ tree, Spec.AuthField request.snapshot request.principal (context request.snapshot object source)
      field.name [] .nil path tree ∧ Spec.erase tree = renderLeaf field outcome path := by
  rcases exact_or_fault _ _ _ _ _ valid with exact | ⟨code, rfl⟩
  · subst outcome
    cases field with
    | projectId => exact ⟨_, .projectId source owned, rfl⟩
    | projectTitle => exact ⟨_, .projectTitle source owned, rfl⟩
    | taskId => exact ⟨_, .taskId source owned, rfl⟩
    | taskTitle => exact ⟨_, .taskTitle source owned, rfl⟩
  · cases code <;> cases field <;>
      first
      | exact ⟨_, .framework (shape := .scalar false) owned rfl .argument, rfl⟩
      | exact ⟨_, .framework (shape := .scalar false) owned rfl .internal, rfl⟩
      | exact ⟨_, .framework (shape := .scalar false) owned rfl .exhausted, rfl⟩

end Example.Tenant.Fault

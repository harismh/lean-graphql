import Example.Tenant.ExecutionBridge
import GraphQL.Plan.Specifications
import GraphQL.Plan.ResultSpec

namespace Example.Tenant.Contract
open GraphQL.Plan

/-- Root requests accept arbitrary IDs. Ownership is a premise only for child parents. -/
def ObjectInvariant (request : Binding.Request) : (object : Fin 3) → Binding.carriers object → Prop
  | ⟨0, _⟩, _ => True
  | ⟨1, _⟩, parent => OwnedProject request.snapshot request.principal parent
  | ⟨2, _⟩, parent => OwnedTask request.snapshot request.principal parent
  | ⟨n + 3, h⟩, _ => False.elim (by omega)

def OutputInvariant (request : Binding.Request) : (type : OutputType 3) → type.denote Binding.carriers → Prop
  | .string, _ => True
  | .int, _ => True
  | .boolean, _ => True
  | .object object, value => ObjectInvariant request object value
  | .nullable type, value => ∀ item, value = some item → OutputInvariant request type item
  | .list type, values => ∀ item, List.Mem item values → OutputInvariant request type item

/-- Domain equations are fixed independently of the resolver record and adapter.
They preserve lookup choice, exact projections, order, duplicates and public denial. -/
def Expected : Meanings Planning.schema Binding.carriers Binding.Request ApplicationError :=
  fun {object} field request parent args => match object, field with
  | ⟨0, _⟩, ⟨⟨0, _⟩⟩ => .ok (project request.snapshot request.principal args)
  | ⟨0, _⟩, ⟨⟨1, _⟩⟩ => .ok (projects request.snapshot request.principal)
  | ⟨0, _⟩, ⟨⟨n + 2, h⟩⟩ => False.elim (by simp [Planning.schema] at h; omega)
  | ⟨1, _⟩, ⟨⟨0, _⟩⟩ => .ok parent.id
  | ⟨1, _⟩, ⟨⟨1, _⟩⟩ => .ok parent.title
  | ⟨1, _⟩, ⟨⟨2, _⟩⟩ => .ok (projectTasks request.snapshot request.principal parent)
  | ⟨1, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [Planning.schema] at h; omega)
  | ⟨2, _⟩, ⟨⟨0, _⟩⟩ => .ok parent.id
  | ⟨2, _⟩, ⟨⟨1, _⟩⟩ => .ok parent.title
  | ⟨2, _⟩, ⟨⟨2, _⟩⟩ => match project request.snapshot request.principal parent.projectId with
    | some row => .ok row
    | none => .error (.application .unavailable)
  | ⟨2, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [Planning.schema] at h; omega)
  | ⟨n + 3, h⟩, _ => False.elim (by simp [Planning.schema] at h; omega)

def AllowedOutcome (request : Binding.Request) (type : OutputType 3) : Outcome ApplicationError (type.denote Binding.carriers) → Prop
  | .ok value => OutputInvariant request type value
  | .error error => error = .application .unavailable

def tenant : Contracts Planning.schema Binding.carriers Binding.Request ApplicationError where
  pre := fun {object} _ request parent _ => ObjectInvariant request object parent
  post := fun field request parent args result =>
    result = Expected field request parent args ∧ AllowedOutcome request field.decl.output result
  compatible := fun {_} _ _ {_} _ => True

theorem expected_owned (field : FieldId Planning.schema object) (request : Binding.Request)
    (parent : Binding.carriers object) (args : field.Args) :
    AllowedOutcome request field.decl.output (Expected field request parent args) := by
  rcases object with ⟨object, bound⟩
  rcases field with ⟨⟨field, valid⟩⟩
  rcases object with _ | (_ | (_ | object)) <;>
    rcases field with _ | (_ | (_ | field)) <;>
    try { simp [Planning.schema] at bound valid <;> omega }
  · exact fun _ found => project_owned found
  · exact fun _ member => projects_owned member
  · trivial
  · trivial
  · exact fun _ member => projectTasks_owned member
  · trivial
  · trivial
  · simp only [Expected]
    split
    next row found => exact project_owned found
    next => rfl

theorem manual_expected (field : FieldId Planning.schema object) (request : Binding.Request)
    (parent : Binding.carriers object) (args : field.Args) :
    Adapter.meanings (Binding.adapt Binding.application) field request parent args =
      Expected field request parent args := by
  rcases object with ⟨object, bound⟩
  rcases field with ⟨⟨field, valid⟩⟩
  rcases object with _ | (_ | (_ | object)) <;>
    rcases field with _ | (_ | (_ | field)) <;>
    try rfl
  all_goals try { simp [Planning.schema] at bound valid <;> omega }
  cases found : project request.snapshot request.principal parent.projectId <;>
    simp [Adapter.meanings, Binding.adapt, Binding.application, Binding.taskProjectBinding,
    Binding.taskProjectSingle, Binding.toOutcome, Binding.resolveTaskProject, taskProject, Expected,
    Except.mapError, Binding.publicError, found] <;> rfl

theorem tenantResolvers_satisfy_contracts (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter) :
    BackendSatisfies tenant (Adapter.meanings adapter) := by
  intro object field request parent args _
  have target := adapter_single_agreement Binding.independentBindings adapter agreement
    object (Binding.checked.coordinate field) request parent args
  have manual := adapter_single_agreement Binding.independentBindings (Binding.adapt Binding.application)
    Binding.application_agreement object (Binding.checked.coordinate field) request parent args
  have eq := (target.trans manual.symm).trans (manual_expected field request parent args)
  have eq' : Adapter.meanings adapter field request parent args = Expected field request parent args := eq
  exact ⟨eq', Eq.mp (congrArg (AllowedOutcome request field.decl.output) eq'.symm)
    (expected_owned field request parent args)⟩

end Example.Tenant.Contract

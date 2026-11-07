import Example.Tenant.Schema
import GraphQL.Plan.Bindings

namespace Example.Tenant.Binding
open GraphQL.Plan

/-- Snapshot-independent carriers. Request data is supplied at execution, not compiled into plans. -/
abbrev carriers : Fin 3 → Type
  | ⟨0, _⟩ => Unit
  | ⟨1, _⟩ => Project
  | _ => Task

structure Request where
  snapshot : Snapshot
  principal : Principal

structure ProjectArgs where
  id : String
  deriving DecidableEq, Repr

def packArgs (key : String) : ProjectArgs := ⟨key⟩
def unpackArgs (args : ProjectArgs) : String := args.id

theorem arguments_roundtrip (key : String) : unpackArgs (packArgs key) = key := rfl
theorem arguments_inverse (args : ProjectArgs) : packArgs (unpackArgs args) = args := rfl

def publicError : Example.Tenant.PublicError ApplicationError → GraphQL.Plan.PublicError ApplicationError
  | .application error => .application error
  | .framework error => .framework (Planning.frameworkCode error)

def toOutcome (result : Except (Example.Tenant.PublicError ApplicationError) α) : Outcome ApplicationError α :=
  result.mapError publicError

def fromOutcome (result : Outcome ApplicationError α) : Except (Example.Tenant.PublicError ApplicationError) α :=
  result.mapError Planning.errorCode

theorem public_error_roundtrip (error : Example.Tenant.PublicError ApplicationError) :
    Planning.errorCode (publicError error) = error := by cases error with
  | application error => rfl
  | framework error => exact Planning.framework_error_roundtrip error

theorem public_error_inverse (error : GraphQL.Plan.PublicError ApplicationError) :
    publicError (Planning.errorCode error) = error := by
  cases error with
  | application error => rfl
  | framework error => cases error <;> rfl

theorem outcome_roundtrip (result : Except (Example.Tenant.PublicError ApplicationError) α) :
    fromOutcome (toOutcome result) = result := by
  cases result <;> simp [fromOutcome, toOutcome, Except.mapError, public_error_roundtrip]

theorem outcome_inverse (result : Outcome ApplicationError α) : toOutcome (fromOutcome result) = result := by
  cases result <;> simp [fromOutcome, toOutcome, Except.mapError, public_error_inverse]

theorem outcome_success (value : α) : toOutcome (.ok value) = .ok value := rfl

theorem outcome_failure (error : Example.Tenant.PublicError ApplicationError) :
    (toOutcome (.error error) : Outcome ApplicationError α) = .error (publicError error) := rfl

def presenceToInput : GraphQL.Presence α → Input α
  | .missing => .omitted | .null => .null | .value value => .value value

def inputToPresence : Input α → GraphQL.Presence α
  | .omitted => .missing | .null => .null | .value value => .value value

theorem presence_roundtrip (value : GraphQL.Presence α) : inputToPresence (presenceToInput value) = value := by
  cases value <;> rfl

theorem input_roundtrip (value : Input α) : presenceToInput (inputToPresence value) = value := by
  cases value <;> rfl

/-- Independently designated application implementations, with the application's
argument record and public failure vocabulary. No adapter dispatch table is used. -/
def resolveProject (request : Request) (_ : Unit) (args : ProjectArgs) :
    Except (Example.Tenant.PublicError ApplicationError) (Option Project) :=
  .ok (Example.Tenant.project request.snapshot request.principal args.id)

def resolveProjects (request : Request) (_ : Unit) (_ : Unit) :
    Except (Example.Tenant.PublicError ApplicationError) (List Project) :=
  .ok (Example.Tenant.projects request.snapshot request.principal)

def resolveProjectId (_ : Request) (parent : Project) (_ : Unit) :
    Except (Example.Tenant.PublicError ApplicationError) String := .ok parent.id

def resolveProjectTitle (_ : Request) (parent : Project) (_ : Unit) :
    Except (Example.Tenant.PublicError ApplicationError) String := .ok parent.title

def resolveTasks (request : Request) (parent : Project) (_ : Unit) :
    Except (Example.Tenant.PublicError ApplicationError) (List Task) :=
  .ok (Example.Tenant.projectTasks request.snapshot request.principal parent)

def resolveTaskId (_ : Request) (parent : Task) (_ : Unit) :
    Except (Example.Tenant.PublicError ApplicationError) String := .ok parent.id

def resolveTaskTitle (_ : Request) (parent : Task) (_ : Unit) :
    Except (Example.Tenant.PublicError ApplicationError) String := .ok parent.title

def resolveTaskProject (request : Request) (parent : Task) (_ : Unit) :
    Except (Example.Tenant.PublicError ApplicationError) Project :=
  (Example.Tenant.taskProject request.snapshot request.principal parent).mapError
    Example.Tenant.PublicError.application

def projectSingle (request : Request) (parent : Unit) (key : String) :=
  toOutcome (resolveProject request parent (packArgs key))
def taskProjectSingle (request : Request) (parent : Task) (args : Unit) :=
  toOutcome (resolveTaskProject request parent args)

/-- This key is sufficient only within one request (including its immutable snapshot).
It must not authorize reuse across different requests just because tenant and ID match. -/
def taskProjectKey : SufficientKey (models := carriers) taskProject taskProjectSingle where
  Key := Nat × String
  equal := inferInstance
  key := fun request parent _ => (request.principal.tenant, parent.projectId)
  sufficient := by
    intro context left leftArgs right rightArgs h
    have same := congrArg Prod.snd h
    change left.projectId = right.projectId at same
    simp [taskProjectSingle, resolveTaskProject, Example.Tenant.taskProject, same] <;> rfl

/-- A semantic batch implementation for the manual artifact. It is a pointwise
loop, so it carries no claim of fewer physical lookups. S4b must supply that separately. -/
def taskProjectBatch : BatchCapability (models := carriers) taskProject taskProjectSingle where
  run := fun request {n} inputs => inputs.map (fun input => taskProjectSingle request input.1 input.2)
  exact := by
    intro request n inputs i
    exact Vector.getElem_map _ i.isLt
  deduplication := some taskProjectKey

def projectBinding : FieldBinding rootProject carriers Request ApplicationError := ⟨projectSingle, none⟩
def projectsBinding : FieldBinding rootProjects carriers Request ApplicationError :=
  ⟨fun r p a => toOutcome (resolveProjects r p a), none⟩
def projectIdBinding : FieldBinding projectId carriers Request ApplicationError :=
  ⟨fun r p a => toOutcome (resolveProjectId r p a), none⟩
def projectTitleBinding : FieldBinding projectTitle carriers Request ApplicationError :=
  ⟨fun r p a => toOutcome (resolveProjectTitle r p a), none⟩
def tasksBinding : FieldBinding projectTasks carriers Request ApplicationError :=
  ⟨fun r p a => toOutcome (resolveTasks r p a), none⟩
def taskIdBinding : FieldBinding taskId carriers Request ApplicationError :=
  ⟨fun r p a => toOutcome (resolveTaskId r p a), none⟩
def taskTitleBinding : FieldBinding taskTitle carriers Request ApplicationError :=
  ⟨fun r p a => toOutcome (resolveTaskTitle r p a), none⟩
def taskProjectBinding : FieldBinding taskProject carriers Request ApplicationError :=
  ⟨taskProjectSingle, some taskProjectBatch⟩

/-- The agreement target is fixed by AST coordinates before adapter construction. -/
def independentBindings : BindingsByField checked carriers Request ApplicationError :=
  fun owner field => match owner, field with
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨fun request parent key => toOutcome (resolveProject request parent ⟨key⟩), none⟩
  | ⟨0, _⟩, ⟨1, _⟩ => ⟨fun request parent args => toOutcome (resolveProjects request parent args), none⟩
  | ⟨0, _⟩, ⟨n + 2, h⟩ => False.elim (by simp [demoAst] at h; omega)
  | ⟨1, _⟩, ⟨0, _⟩ => ⟨fun request parent args => toOutcome (resolveProjectId request parent args), none⟩
  | ⟨1, _⟩, ⟨1, _⟩ => ⟨fun request parent args => toOutcome (resolveProjectTitle request parent args), none⟩
  | ⟨1, _⟩, ⟨2, _⟩ => ⟨fun request parent args => toOutcome (resolveTasks request parent args), none⟩
  | ⟨1, _⟩, ⟨n + 3, h⟩ => False.elim (by simp [demoAst] at h; omega)
  | ⟨2, _⟩, ⟨0, _⟩ => ⟨fun request parent args => toOutcome (resolveTaskId request parent args), none⟩
  | ⟨2, _⟩, ⟨1, _⟩ => ⟨fun request parent args => toOutcome (resolveTaskTitle request parent args), none⟩
  | ⟨2, _⟩, ⟨2, _⟩ => ⟨fun request parent args => toOutcome (resolveTaskProject request parent args), some taskProjectBatch⟩
  | ⟨2, _⟩, ⟨n + 3, h⟩ => False.elim (by simp [demoAst] at h; omega)
  | ⟨n + 3, h⟩, _ => False.elim (by simp [demoAst] at h; omega)

/-- Golden record shape for future generation. Every field retains its canonical type. -/
structure ResolverRecord where
  queryProject : FieldBinding rootProject carriers Request ApplicationError
  queryProjects : FieldBinding rootProjects carriers Request ApplicationError
  projectId : FieldBinding projectId carriers Request ApplicationError
  projectTitle : FieldBinding projectTitle carriers Request ApplicationError
  projectTasks : FieldBinding projectTasks carriers Request ApplicationError
  taskId : FieldBinding taskId carriers Request ApplicationError
  taskTitle : FieldBinding taskTitle carriers Request ApplicationError
  taskProject : FieldBinding taskProject carriers Request ApplicationError

def application : ResolverRecord :=
  ⟨projectBinding, projectsBinding, projectIdBinding, projectTitleBinding, tasksBinding,
    taskIdBinding, taskTitleBinding, taskProjectBinding⟩

def adapt (record : ResolverRecord) : Adapter indexedSchema.schema carriers Request ApplicationError :=
  fun {owner} field => match owner, field with
  | ⟨0, _⟩, ⟨⟨0, _⟩⟩ => record.queryProject
  | ⟨0, _⟩, ⟨⟨1, _⟩⟩ => record.queryProjects
  | ⟨0, _⟩, ⟨⟨n + 2, h⟩⟩ => False.elim (by simp [indexedSchema, Planning.schema] at h; omega)
  | ⟨1, _⟩, ⟨⟨0, _⟩⟩ => record.projectId
  | ⟨1, _⟩, ⟨⟨1, _⟩⟩ => record.projectTitle
  | ⟨1, _⟩, ⟨⟨2, _⟩⟩ => record.projectTasks
  | ⟨1, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [indexedSchema, Planning.schema] at h; omega)
  | ⟨2, _⟩, ⟨⟨0, _⟩⟩ => record.taskId
  | ⟨2, _⟩, ⟨⟨1, _⟩⟩ => record.taskTitle
  | ⟨2, _⟩, ⟨⟨2, _⟩⟩ => record.taskProject
  | ⟨2, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [indexedSchema, Planning.schema] at h; omega)
  | ⟨n + 3, h⟩, _ => False.elim (by simp [demoAst] at h; omega)

theorem application_agreement : BindingAgreement independentBindings (adapt application) := by
  intro owner field
  rcases owner with ⟨owner, bound⟩
  rcases field with ⟨field, valid⟩
  rcases owner with _ | (_ | (_ | owner)) <;>
    rcases field with _ | (_ | (_ | field)) <;>
    first | rfl | simp [demoAst] at bound valid <;> omega

theorem root_argument_translation (request : Request) (key : String) :
    Adapter.meanings (adapt application) rootProject request () key =
      toOutcome (resolveProject request () (packArgs key)) := rfl

theorem title_adapter (request : Request) (parent : Project) :
    Adapter.meanings (adapt application) projectTitle request parent () =
      toOutcome (resolveProjectTitle request parent ()) := rfl

theorem batch_slot_preserved : (adapt application taskProject).batch = some taskProjectBatch := rfl

end Example.Tenant.Binding

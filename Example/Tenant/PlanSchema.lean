import Example.Tenant.Resolved
import Example.Tenant.Evaluation
import GraphQL.Plan.Graph

namespace Example.Tenant.Planning
open GraphQL.Plan

abbrev objectId : ObjectType → Fin 3
  | .query => 0 | .project => 1 | .task => 2

abbrev schema : Schema := ⟨3, fun object => match object.val with
  | 0 => [⟨"project", .string, .nullable (.object 1)⟩, ⟨"projects", .unit, .list (.object 1)⟩]
  | 1 => [⟨"id", .unit, .string⟩, ⟨"title", .unit, .string⟩, ⟨"tasks", .unit, .list (.object 2)⟩]
  | _ => [⟨"id", .unit, .string⟩, ⟨"title", .unit, .string⟩, ⟨"project", .unit, .object 1⟩]⟩

abbrev models (s : Snapshot) : Fin 3 → Type
  | ⟨0, _⟩ => Unit
  | ⟨1, _⟩ => Occurrence s.projects
  | _ => Occurrence s.tasks

abbrev Model (s : Snapshot) (object : ObjectType) := models s (objectId object)

def context (s : Snapshot) : (object : ObjectType) → Model s object → Spec.Context s
  | .query, _ => .query
  | .project, row => .project row
  | .task, row => .task row

def leafId : IR.Leaf object → FieldId schema (objectId object)
  | .projectId => ⟨⟨0, by decide⟩⟩
  | .projectTitle => ⟨⟨1, by decide⟩⟩
  | .taskId => ⟨⟨0, by decide⟩⟩
  | .taskTitle => ⟨⟨1, by decide⟩⟩

def branchId : IR.Branch parent child → FieldId schema (objectId parent)
  | .project => ⟨⟨0, by decide⟩⟩
  | .projects => ⟨⟨1, by decide⟩⟩
  | .tasks => ⟨⟨2, by decide⟩⟩
  | .taskProject => ⟨⟨2, by decide⟩⟩

def leafArgs (field : IR.Leaf object) : (leafId field).Args := by cases field <;> exact ()

def branchArgs (field : IR.Branch parent child) : field.Args → (branchId field).Args := by
  cases field <;> exact id

def leafString {carriers : Fin 3 → Type} (field : IR.Leaf object) : (leafId field).Out carriers → String := by
  cases field <;> exact id

def errorCode : GraphQL.Plan.PublicError ApplicationError → Example.Tenant.PublicError ApplicationError
  | .application e => .application e
  | .framework .argument => .framework .argument
  | .framework .internal => .framework .internal
  | .framework .exhausted => .framework .exhausted

def frameworkCode : Example.Tenant.FrameworkError → GraphQL.Plan.FrameworkError
  | .argument => .argument | .internal => .internal | .exhausted => .exhausted

def branchRows {carriers : Fin 3 → Type} (field : IR.Branch parent child) :
    Outcome ApplicationError ((branchId field).Out carriers) → List (carriers (objectId child)) :=
  match field with
  | .project => fun outcome => match outcome with
      | .ok (some row) => [row] | _ => []
  | .projects | .tasks => fun outcome => match outcome with | .ok rows => rows | .error _ => []
  | .taskProject => fun outcome => match outcome with | .ok row => [row] | .error _ => []

def isList : IR.Branch parent child → Bool
  | .projects | .tasks => true | _ => false
def isNullable : IR.Branch parent child → Bool
  | .project => true | _ => false

def meanings (s : Snapshot) : Meanings schema (models s) Principal ApplicationError :=
  fun {object} field principal parent args =>
    match object, field with
    | ⟨0, _⟩, ⟨⟨0, _⟩⟩ => .ok (projectOccurrence s principal args)
    | ⟨0, _⟩, ⟨⟨1, _⟩⟩ => .ok (projectOccurrences s principal)
    | ⟨0, _⟩, ⟨⟨n + 2, h⟩⟩ => False.elim (by simp [schema] at h; omega)
    | ⟨1, _⟩, ⟨⟨0, _⟩⟩ => .ok parent.value.id
    | ⟨1, _⟩, ⟨⟨1, _⟩⟩ => .ok parent.value.title
    | ⟨1, _⟩, ⟨⟨2, _⟩⟩ => .ok (taskOccurrences s principal parent)
    | ⟨1, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [schema] at h; omega)
    | ⟨2, _⟩, ⟨⟨0, _⟩⟩ => .ok parent.value.id
    | ⟨2, _⟩, ⟨⟨1, _⟩⟩ => .ok parent.value.title
    | ⟨2, _⟩, ⟨⟨2, _⟩⟩ => match projectOccurrence s principal parent.value.projectId with
        | some row => .ok row | none => .error (.application .unavailable)
    | ⟨2, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [schema] at h; omega)
    | ⟨n + 3, h⟩, _ => False.elim (by simp [schema] at h; omega)

theorem leaf_identity (field : IR.Leaf object) : (leafId field).decl.name = field.name := by
  cases field <;> rfl
theorem branch_identity (field : IR.Branch parent child) : (branchId field).decl.name = field.name := by
  cases field <;> rfl
theorem context_type (row : Model s object) : (context s object row).type = object := by
  cases object <;> rfl

theorem framework_error_roundtrip (code : Example.Tenant.FrameworkError) :
    errorCode (.framework (frameworkCode code)) = .framework code := by cases code <;> rfl

theorem framework_code_roundtrip (code : GraphQL.Plan.FrameworkError) :
    (match errorCode (.framework code) with
      | .framework value => frameworkCode value
      | .application _ => .internal) = code := by cases code <;> rfl

end Example.Tenant.Planning

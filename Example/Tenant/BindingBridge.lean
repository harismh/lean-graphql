import Example.Tenant.Bindings
import GraphQL.Plan.Conversion

namespace Example.Tenant.Binding
open GraphQL.Plan

def transport (s : Snapshot) : (object : Fin 3) → Planning.models s object → carriers object
  | ⟨0, _⟩, _ => ()
  | ⟨1, _⟩, value => value.value
  | ⟨_ + 2, _⟩, value => value.value

theorem owned_occurrences_values (tenant : α → TenantId) (principal : Principal) (rows : List α) :
    (ownedOccurrences tenant principal rows).map Occurrence.value =
      rows.filter (fun row => tenant row == principal.tenant) := by
  unfold ownedOccurrences
  refine Eq.trans (List.filter_map (f := @Occurrence.value α rows)
    (p := fun row => tenant row == principal.tenant)
    (l := List.ofFn (fun i : Fin rows.length => Occurrence.mk i))).symm ?_
  congr 1
  simp [List.map_ofFn, Function.comp_def, Occurrence.value]

theorem task_occurrences_values (s : Snapshot) (principal : Principal) (parent : Occurrence s.projects) :
    (taskOccurrences s principal parent).map Occurrence.value = Example.Tenant.projectTasks s principal parent.value := by
  simp [taskOccurrences, Example.Tenant.projectTasks, List.map_filterMap,
    lookupOccurrence_value]

theorem binding_agrees_s1 (s : Snapshot) (principal : Principal)
    (object : Fin 3) (field : CanonicalField demoAst object)
    (parent : Planning.models s object) (args : (checked.field object field).Args) :
    Adapter.meanings (adapt application) (checked.field object field) ⟨s, principal⟩ (transport s object parent) args =
      convertOutcome (checked.field object field).decl.output (transport s)
        (Planning.meanings s (checked.field object field) principal parent args) := by
  rcases object with ⟨object, bound⟩
  rcases field with ⟨field, valid⟩
  rcases object with _ | (_ | (_ | object)) <;>
    rcases field with _ | (_ | (_ | field))
  all_goals try (simp [demoAst] at bound valid <;> omega)
  · change Except.ok (Example.Tenant.project s principal args) =
      (Except.ok ((projectOccurrence s principal args).map Occurrence.value) : Outcome ApplicationError (Option Project))
    exact congrArg Except.ok (lookupOccurrence_value Project.tenant Project.id principal args s.projects).symm
  · change Except.ok (Example.Tenant.projects s principal) =
      (Except.ok ((projectOccurrences s principal).map Occurrence.value) : Outcome ApplicationError (List Project))
    exact congrArg Except.ok (owned_occurrences_values Project.tenant principal s.projects).symm
  · rfl
  · rfl
  · change Except.ok (Example.Tenant.projectTasks s principal parent.value) =
      (Except.ok ((taskOccurrences s principal parent).map Occurrence.value) : Outcome ApplicationError (List Task))
    exact congrArg Except.ok (task_occurrences_values s principal parent).symm
  · rfl
  · rfl
  · have conversion := lookupOccurrence_value Project.tenant Project.id principal parent.value.projectId s.projects
    change (projectOccurrence s principal parent.value.projectId).map Occurrence.value =
      Example.Tenant.project s principal parent.value.projectId at conversion
    change toOutcome ((Example.Tenant.taskProject s principal parent.value).mapError
      Example.Tenant.PublicError.application) =
      (Planning.meanings s (Planning.branchId IR.Branch.taskProject) principal parent args).map Occurrence.value
    have raw : Planning.meanings s (Planning.branchId IR.Branch.taskProject) principal parent args =
        (match projectOccurrence s principal parent.value.projectId with
          | some row => .ok row
          | none => (Except.error (.application .unavailable) : Outcome ApplicationError (Occurrence s.projects))) := rfl
    rw [raw]
    cases found : projectOccurrence s principal parent.value.projectId with
    | none =>
      have absent : Example.Tenant.project s principal parent.value.projectId = none := by simpa [found] using conversion.symm
      simp [Example.Tenant.taskProject, absent, toOutcome, publicError, Except.mapError, Except.map]
    | some row =>
      have present : Example.Tenant.project s principal parent.value.projectId = some row.value := by simpa [found] using conversion.symm
      simp [Example.Tenant.taskProject, present, toOutcome, publicError, Except.mapError, Except.map]

end Example.Tenant.Binding

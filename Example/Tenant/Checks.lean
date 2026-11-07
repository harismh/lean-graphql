import Example.Tenant.Model
import Example.Tenant.Selection
import Example.Tenant.Authorization

namespace Example.Tenant.Checks

def caller : Principal := ⟨1⟩
def foreignProject : Project := ⟨"shared", 2, "private", []⟩
def ownedProject : Project := ⟨"shared", 1, "public", ["foreign", "child", "missing"]⟩
def ownedTask : Task := ⟨"child", 1, "visible", "foreign-only"⟩
def foreignTask : Task := ⟨"foreign", 2, "secret", "shared"⟩
def snapshot : Snapshot :=
  ⟨[foreignProject, ownedProject, ⟨"foreign-only", 2, "private target", []⟩],
    [foreignTask, ownedTask]⟩

theorem duplicate_id_looks_past_foreign :
    project snapshot caller "shared" = some ownedProject := by decide

theorem filtered_tasks :
    projectTasks snapshot caller ownedProject = [ownedTask] := by decide

theorem foreign_task_owned_target_still_omitted :
    foreignTask ∉ projectTasks snapshot caller ownedProject := by decide

theorem owned_task_foreign_target_fails :
    taskProject snapshot caller ownedTask = .error .unavailable := rfl

theorem missing_and_foreign_root_equal :
    project snapshot caller "foreign-only" = project snapshot caller "missing" := by decide

theorem missing_and_foreign_required_target_equal :
    taskProject snapshot caller ownedTask =
      taskProject snapshot caller { ownedTask with projectId := "missing" } := rfl

theorem authorized_leaf : ProjectLeaf snapshot caller ownedProject .title "public" :=
  .mk ⟨⟨1, by decide⟩⟩ (by decide) .title

def forged : Project := { ownedProject with title := "invented" }

theorem copied_tenant_is_insufficient :
    forged.tenant = caller.tenant ∧
      ¬ ProjectLeaf snapshot caller forged .title "invented" :=
  ⟨rfl, forged_project_rejected (by decide)⟩

theorem wrong_field_rejected :
    ¬ ProjectLeaf snapshot caller ownedProject .title "shared" :=
  wrong_projection_rejected (by decide)

def foreignOccurrence : Occurrence snapshot.projects := ⟨⟨0, by decide⟩⟩
def ownedOccurrence : Occurrence snapshot.projects := ⟨⟨1, by decide⟩⟩

/-- A real snapshot position is not authorization for that record or its values. -/
theorem fake_label_is_insufficient :
    ¬ Spec.AuthField snapshot caller (.project foreignOccurrence) "title" [] .nil []
      (.scalar "private") := by
  intro h
  have owned := Spec.authField_owned h
  exact (by decide : foreignProject.tenant ≠ caller.tenant) owned

theorem real_foreign_member_rejected :
    ¬ ProjectLeaf snapshot caller foreignProject .title "private" := by
  intro h
  exact (by decide : foreignProject.tenant ≠ caller.tenant) (projectLeaf_sound h).1.2

theorem wrong_parent_rejected :
    ¬ ProjectLeaf snapshot caller ownedProject .title foreignProject.title :=
  wrong_projection_rejected (by decide)

def titleSelection : PSelection := .field "title" [] .nil .nil
def query : PSelection := .field "projects" [] titleSelection .nil

theorem valid_query : ValidOperation query := by
  refine ⟨by decide, .object .projects (by decide) (by simp [PSelection.names]) ?_ .nil⟩
  exact .leaf .projectTitle (by simp [PSelection.names]) .nil

theorem unknown_root_rejected :
    ¬ ValidPSelection .query (.field "secret" [] .nil .nil) :=
  no_unknown_root (by decide)

theorem scalar_children_rejected :
    ¬ ValidPSelection .project (.field "title" [] titleSelection .nil) := by
  have objectName : ∀ n a c, ObjectField .project n a c → n = "tasks" := by
    intro n a c decl
    cases decl
    rfl
  intro h
  cases h with
  | object decl _ _ _ _ =>
    exact (by decide : ¬ ("title" = "tasks")) (objectName _ _ _ decl)

end Example.Tenant.Checks

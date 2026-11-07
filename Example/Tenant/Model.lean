import Std

/-! Independent domain model for S0. No executor, generator, or resolver imports. -/
namespace Example.Tenant

abbrev TenantId := Nat
abbrev RecordId := String

structure Principal where
  tenant : TenantId
  deriving DecidableEq, Repr

structure Project where
  id : RecordId
  tenant : TenantId
  title : String
  taskIds : List RecordId
  deriving DecidableEq, Repr

structure Task where
  id : RecordId
  tenant : TenantId
  title : String
  projectId : RecordId
  deriving DecidableEq, Repr

structure Snapshot where
  projects : List Project
  tasks : List Task
  deriving DecidableEq, Repr

/-- The index distinguishes duplicate occurrences, even of equal records. -/
structure Occurrence (rows : List α) where
  index : Fin rows.length

def Occurrence.value {rows : List α} (r : Occurrence rows) : α := rows[r.index]

/-- Search tests ownership before ID, including when IDs are duplicated. -/
def lookupOwned (tenant : α → TenantId) (id : α → RecordId)
    (p : Principal) (key : RecordId) : List α → Option α
  | [] => none
  | row :: rows =>
    if tenant row = p.tenant ∧ id row = key then some row
    else lookupOwned tenant id p key rows

theorem lookupOwned_sound (tenant : α → TenantId) (id : α → RecordId)
    (p : Principal) (key : RecordId) (rows : List α) (row : α)
    (h : lookupOwned tenant id p key rows = some row) :
    row ∈ rows ∧ tenant row = p.tenant ∧ id row = key := by
  induction rows with
  | nil => simp [lookupOwned] at h
  | cons head tail ih =>
    simp only [lookupOwned] at h
    split at h
    next hit =>
      cases Option.some.inj h
      exact ⟨List.mem_cons_self, hit⟩
    next _ =>
      obtain ⟨member, owned, keyEq⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ member, owned, keyEq⟩

theorem lookupOwned_none (tenant : α → TenantId) (id : α → RecordId)
    (p : Principal) (key : RecordId) (rows : List α)
    (h : ∀ row ∈ rows, ¬ (tenant row = p.tenant ∧ id row = key)) :
    lookupOwned tenant id p key rows = none := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    rw [lookupOwned, if_neg (h head List.mem_cons_self)]
    exact ih (fun row member => h row (List.mem_cons_of_mem _ member))

def project (s : Snapshot) (p : Principal) (id : RecordId) : Option Project :=
  lookupOwned Project.tenant Project.id p id s.projects

def projects (s : Snapshot) (p : Principal) : List Project :=
  s.projects.filter (fun row => row.tenant == p.tenant)

def projectTasks (s : Snapshot) (p : Principal) (parent : Project) : List Task :=
  parent.taskIds.filterMap (lookupOwned Task.tenant Task.id p · s.tasks)

inductive ApplicationError where
  | unavailable
  deriving DecidableEq, Repr

inductive FrameworkError where
  | argument | exhausted | internal
  deriving DecidableEq, Repr

inductive PublicError (app : Type) where
  | application (error : app)
  | framework (error : FrameworkError)
  deriving DecidableEq, Repr

def taskProject (s : Snapshot) (p : Principal) (parent : Task) :
    Except ApplicationError Project :=
  match project s p parent.projectId with
  | some row => .ok row
  | none => .error .unavailable

/-- Auxiliary value-level domain predicate. Whole-response authorization uses
occurrence-indexed AuthField; this predicate alone does not bind lookup position. -/
def OwnedProject (s : Snapshot) (p : Principal) (row : Project) : Prop :=
  row ∈ s.projects ∧ row.tenant = p.tenant

def OwnedTask (s : Snapshot) (p : Principal) (row : Task) : Prop :=
  row ∈ s.tasks ∧ row.tenant = p.tenant

theorem project_owned (h : project s p key = some row) : OwnedProject s p row := by
  obtain ⟨hm, ht, _⟩ := lookupOwned_sound _ _ _ _ _ _ h
  exact ⟨hm, ht⟩

theorem projects_owned (h : row ∈ projects s p) : OwnedProject s p row := by
  simpa [projects, OwnedProject] using h

theorem projectTasks_owned (h : row ∈ projectTasks s p parent) : OwnedTask s p row := by
  obtain ⟨key, _, found⟩ := List.mem_filterMap.mp h
  obtain ⟨hm, ht, _⟩ := lookupOwned_sound _ _ _ _ _ _ found
  exact ⟨hm, ht⟩

theorem taskProject_owned (h : taskProject s p parent = .ok row) : OwnedProject s p row := by
  unfold taskProject at h
  split at h
  next value found =>
    cases Except.ok.inj h
    exact project_owned found
  next => contradiction

/-- Missing and foreign-only IDs have exactly the same public outcome. -/
theorem unavailable_when_no_owned_target
    (h : ∀ row ∈ s.projects, ¬ (row.tenant = p.tenant ∧ row.id = parent.projectId)) :
    taskProject s p parent = .error .unavailable := by
  simp [taskProject, project, lookupOwned_none _ _ _ _ _ h]

inductive ScalarField where
  | id | title
  deriving DecidableEq, Repr

def projectScalar (row : Project) : ScalarField → String
  | .id => row.id
  | .title => row.title

def taskScalar (row : Task) : ScalarField → String
  | .id => row.id
  | .title => row.title

/-- Auxiliary value-level leaf relation for domain lemmas. The authoritative
whole-tree relation is AuthField in Authorization.lean, indexed by occurrence. -/
inductive ProjectLeaf (s : Snapshot) (p : Principal) : Project → ScalarField → String → Prop
  | mk (occ : Occurrence s.projects) (owned : occ.value.tenant = p.tenant)
      (field : ScalarField) : ProjectLeaf s p occ.value field (projectScalar occ.value field)

theorem projectLeaf_sound (h : ProjectLeaf s p row field value) :
    OwnedProject s p row ∧ value = projectScalar row field := by
  cases h with
  | mk occ owned field =>
    exact ⟨⟨List.getElem_mem _, owned⟩, rfl⟩

theorem forged_project_rejected (absent : row ∉ s.projects) :
    ¬ ProjectLeaf s p row field value := by
  intro h
  exact absent (projectLeaf_sound h).1.1

theorem wrong_projection_rejected (wrong : value ≠ projectScalar row field) :
    ¬ ProjectLeaf s p row field value := by
  intro h
  exact wrong (projectLeaf_sound h).2

end Example.Tenant

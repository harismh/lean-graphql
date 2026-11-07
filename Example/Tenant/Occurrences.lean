import Example.Tenant.Model

namespace Example.Tenant

def Occurrence.tail {head : α} {rows : List α} (r : Occurrence rows) :
    Occurrence (head :: rows) := ⟨⟨r.index.val + 1, Nat.succ_lt_succ r.index.isLt⟩⟩

def lookupOccurrence (tenant : α → TenantId) (id : α → RecordId)
    (p : Principal) (key : RecordId) (rows : List α) : Option (Occurrence rows) :=
  match rows with
  | [] => none
  | row :: rest =>
    if tenant row = p.tenant ∧ id row = key then some ⟨⟨0, by simp⟩⟩
    else (lookupOccurrence tenant id p key rest).map Occurrence.tail

theorem lookupOccurrence_value (tenant : α → TenantId) (id : α → RecordId)
    (p : Principal) (key : RecordId) (rows : List α) :
    (lookupOccurrence tenant id p key rows).map Occurrence.value =
      lookupOwned tenant id p key rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    simp only [lookupOccurrence, lookupOwned]
    split
    · rfl
    · simp only [Option.map_map]
      change (lookupOccurrence tenant id p key tail).map Occurrence.value = _
      exact ih

theorem lookupOccurrence_owned
    {tenant : α → TenantId} {id : α → RecordId} {p : Principal} {key : RecordId}
    {rows : List α} {occurrence : Occurrence rows}
    (h : lookupOccurrence tenant id p key rows = some occurrence) :
    tenant occurrence.value = p.tenant ∧ id occurrence.value = key := by
  have value := lookupOccurrence_value tenant id p key rows
  rw [h] at value
  exact (lookupOwned_sound _ _ _ _ _ _ value.symm).2

/-- This relation records every skipped row, not merely the selected row's value. -/
inductive FirstOwned (tenant : α → TenantId) (id : α → RecordId)
    (p : Principal) (key : RecordId) : (rows : List α) → Occurrence rows → Prop
  | here (hit : tenant head = p.tenant ∧ id head = key) :
      FirstOwned tenant id p key (head :: rest) ⟨⟨0, by simp⟩⟩
  | later (miss : ¬ (tenant head = p.tenant ∧ id head = key))
      (tail : FirstOwned tenant id p key rest occurrence) :
      FirstOwned tenant id p key (head :: rest) occurrence.tail

theorem lookupOccurrence_first {tenant : α → TenantId} {id : α → RecordId}
    {p : Principal} {key : RecordId} {rows : List α} {occurrence : Occurrence rows}
    (h : lookupOccurrence tenant id p key rows = some occurrence) :
    FirstOwned tenant id p key rows occurrence := by
  induction rows with
  | nil => simp [lookupOccurrence] at h
  | cons head rest ih =>
    simp only [lookupOccurrence] at h
    split at h
    next hit => cases Option.some.inj h; exact .here hit
    next miss =>
      cases found : lookupOccurrence tenant id p key rest with
      | none => simp [found] at h
      | some row =>
        simp only [found, Option.map_some] at h
        cases Option.some.inj h
        exact .later miss (ih found)

theorem firstOwned_lookup {tenant : α → TenantId} {id : α → RecordId}
    (h : FirstOwned tenant id p key rows occurrence) :
    lookupOccurrence tenant id p key rows = some occurrence := by
  induction h with
  | here hit => simp [lookupOccurrence, hit]
  | later miss _ ih => simp [lookupOccurrence, miss, ih]

theorem lookupOccurrence_none_iff {tenant : α → TenantId} {id : α → RecordId} :
    lookupOccurrence tenant id p key rows = none ↔
      ∀ row ∈ rows, ¬ (tenant row = p.tenant ∧ id row = key) := by
  induction rows with
  | nil => simp [lookupOccurrence]
  | cons head tail ih =>
    simp only [lookupOccurrence]
    split
    next hit => simp [hit]
    next miss =>
      constructor
      · intro h row member
        cases List.mem_cons.mp member with
        | inl eq => subst row; exact miss
        | inr ht => exact (ih.mp (Option.map_eq_none_iff.mp h)) row ht
      · intro h
        exact Option.map_eq_none_iff.mpr (ih.mpr (fun row hr => h row (List.mem_cons_of_mem _ hr)))

def ownedOccurrences (tenant : α → TenantId) (p : Principal) (rows : List α) :
    List (Occurrence rows) :=
  (List.ofFn (fun i : Fin rows.length => Occurrence.mk i)).filter
    (fun r => tenant r.value == p.tenant)

def projectOccurrence (s : Snapshot) (p : Principal) (id : RecordId) :=
  lookupOccurrence Project.tenant Project.id p id s.projects

def projectOccurrences (s : Snapshot) (p : Principal) :=
  ownedOccurrences Project.tenant p s.projects

def taskOccurrences (s : Snapshot) (p : Principal) (parent : Occurrence s.projects) :=
  parent.value.taskIds.filterMap
    (fun id => lookupOccurrence Task.tenant Task.id p id s.tasks)

theorem ownedOccurrences_owned (h : r ∈ ownedOccurrences tenant p rows) :
    tenant r.value = p.tenant := by
  exact beq_iff_eq.mp (List.mem_filter.mp h).2

theorem taskOccurrences_owned (h : r ∈ taskOccurrences s p parent) :
    r.value.tenant = p.tenant := by
  obtain ⟨_, _, found⟩ := List.mem_filterMap.mp h
  exact (lookupOccurrence_owned found).1

end Example.Tenant

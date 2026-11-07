import Example.Tenant.InputSurface
import Example.Tenant.Template

namespace Example.Tenant.Preparation
open GraphQL.Plan.InputCoercion

instance (object : ObjectType) (selection : PSelection) : Decidable (ValidPSelection object selection) :=
  match found : IR.lower object selection with
  | some checked => isTrue (IR.lower_sound found)
  | none => isFalse (fun valid => by obtain ⟨checked, accepted⟩ := IR.lower_complete valid; rw [found] at accepted; cases accepted)

instance (operation : InputSurface.Operation) : Decidable (InputSurface.ValidOperation operation) := by
  unfold InputSurface.ValidOperation Example.Tenant.ValidOperation
  infer_instance

inductive Error where
  | profile | limits | validation
  deriving DecidableEq, Repr

structure Prepared (operation : InputSurface.Operation) where
  valid : InputSurface.ValidOperation operation
  profile : InputSurface.InProfile operation
  limits : InputSurface.WithinLimits operation
  template : IR.Checked .query (InputSurface.skeleton operation.selection)

def prepare (operation : InputSurface.Operation) : Except Error (Prepared operation) :=
  if profile : InputSurface.InProfile operation then
    if limits : InputSurface.WithinLimits operation then
      if valid : InputSurface.ValidOperation operation then
        match found : IR.lower .query (InputSurface.skeleton operation.selection) with
        | some template => .ok ⟨valid, profile, limits, template⟩
        | none => False.elim (by
          obtain ⟨template, accepted⟩ := IR.lower_complete valid.1.2
          rw [found] at accepted
          cases accepted)
      else .error .validation
    else .error .limits
  else .error .profile

theorem prepare_sound (prepared : Prepared operation) :
    InputSurface.ValidOperation operation ∧ InputSurface.InProfile operation ∧ InputSurface.WithinLimits operation :=
  ⟨prepared.valid, prepared.profile, prepared.limits⟩

theorem prepare_complete (valid : InputSurface.ValidOperation operation) (profile : InputSurface.InProfile operation)
    (limits : InputSurface.WithinLimits operation) : ∃ prepared, prepare operation = .ok prepared := by
  obtain ⟨template, accepted⟩ := IR.lower_complete valid.1.2
  unfold prepare
  simp only [dif_pos profile, dif_pos limits, dif_pos valid]
  split
  · exact ⟨_, rfl⟩
  · rename_i missing
    rw [accepted] at missing
    cases missing

end Example.Tenant.Preparation

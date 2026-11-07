import Example.Tenant.FaultExecution

namespace Example.Tenant.Fault
open Spec

def ObjectValue (type : ObjectType) (selection : PSelection) (value : Value) : Prop :=
  ∃ fields, value = .object fields ∧ ObjectConforms type selection fields

def ListValue (type : ObjectType) (selection : PSelection) (value : Value) : Prop :=
  ∃ values, value = .array values ∧ ItemsConform type false selection values

theorem good_weaken (result : Result α) (good : Good P result) (implies : ∀ value, P value → Q value) : Good Q result := by
  cases result with
  | ok value errors => exact implies value good
  | bubble errors => exact good

theorem auth_shape (proof : AuthTree s p ctx selection path tree) :
    Good (ObjectValue ctx.type selection) (erase tree) := by
  induction proof using AuthTree.rec
    (motive_2 := fun ctx name args children path tree _ =>
      ∃ shape, fieldShape ctx.type name = some shape ∧ Good (ValueConforms shape children) (erase tree))
    (motive_3 := fun rows children path index tree _ => ∀ type,
      (∀ ctx ∈ rows, ctx.type = type) → Good (ListValue type children) (erase tree)) with
  | empty owned => exact ⟨[], rfl, .nil⟩
  | field head tail headIH tailIH =>
    obtain ⟨shape, declared, good⟩ := headIH
    apply good_pair good tailIH
    intro value rest headGood tailGood
    obtain ⟨fields, rfl, fieldsGood⟩ := tailGood
    exact ⟨_, rfl, .cons declared headGood fieldsGood⟩
  | projectId => exact ⟨.scalar false, rfl, .scalar⟩
  | projectTitle => exact ⟨.scalar false, rfl, .scalar⟩
  | taskId => exact ⟨.scalar false, rfl, .scalar⟩
  | taskTitle => exact ⟨.scalar false, rfl, .scalar⟩
  | rootAbsent missing => exact ⟨.object .project true, rfl, .null rfl⟩
  | rootProject found nested ih =>
    refine ⟨.object .project true, rfl, ?_⟩
    apply good_boundary
    · exact good_weaken _ ih (fun _ ⟨fields, eq, valid⟩ => eq ▸ ValueConforms.object valid)
    · exact fun h => .null h
  | rootProjects nested ih =>
    refine ⟨.list .project false false, rfl, ?_⟩
    simp only [erase, required_propagates]
    apply good_weaken _ (ih .project (by intro ctx member; obtain ⟨row, _, rfl⟩ := List.mem_map.mp member; rfl))
    exact fun _ ⟨values, eq, valid⟩ => eq ▸ ValueConforms.list valid
  | tasks r owned nested ih =>
    refine ⟨.list .task false false, rfl, ?_⟩
    simp only [erase, required_propagates]
    apply good_weaken _ (ih .task (by intro ctx member; obtain ⟨row, _, rfl⟩ := List.mem_map.mp member; rfl))
    exact fun _ ⟨values, eq, valid⟩ => eq ▸ ValueConforms.list valid
  | taskProject r owned found nested ih =>
    refine ⟨.object .project false, rfl, ?_⟩
    simp only [erase, required_propagates]
    exact good_weaken _ ih (fun _ ⟨fields, eq, valid⟩ => eq ▸ ValueConforms.object valid)
  | unavailable r owned missing => exact ⟨.object .project false, rfl, good_failure _ _ _⟩
  | framework owned declared code => exact ⟨_, declared, good_failure _ _ _⟩
  | nil => exact ⟨[], rfl, .nil⟩
  | cons head tail headIH tailIH =>
    rename_i type all
    simp only [erase, required_propagates]
    have headType := all _ List.mem_cons_self
    apply good_pair headIH (tailIH type (fun ctx member => all ctx (List.mem_cons_of_mem _ member)))
    intro headValue tailValue headGood tailGood
    obtain ⟨fields, rfl, validHead⟩ := headGood
    obtain ⟨values, rfl, validTail⟩ := tailGood
    exact ⟨_, rfl, .cons (.object (headType ▸ validHead)) validTail⟩

theorem authorized_conforms (proof : AuthorizedResponse s p selection response) : Conforms selection response := by
  obtain ⟨valid, tree, auth, rfl⟩ := proof
  have good := auth_shape auth
  constructor
  · exact valid
  · cases result : erase tree with
    | ok value errors =>
      rw [result] at good
      obtain ⟨fields, rfl, conforming⟩ := good
      exact conforming
    | bubble errors =>
      rw [result] at good
      exact good

theorem fault_execution_conforms (request : Binding.Request) (selected : IR.Checked .query selection)
    (nonempty : selection ≠ .nil) :
    GraphQL.Plan.Sat contracts.Pre contracts.Post (Runtime.execute request selected) (Conforms selection) :=
  GraphQL.Plan.sat_weaken _ (execution_authorized request selected nonempty) (fun _ => authorized_conforms)

end Example.Tenant.Fault

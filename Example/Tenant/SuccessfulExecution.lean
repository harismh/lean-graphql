import Example.Tenant.Execution

namespace Example.Tenant.Success
open Spec

def Successful (result : Result α) : Prop := ∃ value, result = .ok value []

theorem successful_pair (a : Result α) (b : Result β) (ha : Successful a) (hb : Successful b) (f : α → β → γ) :
    Successful (pair f a b) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  exact ⟨f a b, rfl⟩

theorem successful_map (result : Result α) (good : Successful result) (f : α → β) : Successful (result.map f) := by
  obtain ⟨value, rfl⟩ := good
  exact ⟨f value, rfl⟩

theorem successful_boundary (result : Result Value) (good : Successful result) (nullable : Bool) :
    Successful (boundary nullable result) := by
  obtain ⟨value, rfl⟩ := good
  exact ⟨value, rfl⟩

theorem successful_collect (rows : List α) (f : α → Nat → Result Value) (start : Nat)
    (good : ∀ row ∈ rows, ∀ index, Successful (f row index)) :
    Successful (collect (rows.zipIdx start |>.map (fun (row, index) => f row index))) := by
  induction rows generalizing start with
  | nil => exact ⟨[], rfl⟩
  | cons row rows ih =>
    apply successful_pair _ _ (good row List.mem_cons_self start)
    exact ih (start + 1) (fun row member => good row (List.mem_cons_of_mem _ member))

theorem object_success (ctx : Context s) (owned : OwnedContext p ctx)
    (decl : ObjectField ctx.type name args childType)
    (required : ∀ task ∈ s.tasks, task.tenant = p.tenant → ∃ row, projectOccurrence s p task.projectId = some row)
    (child : Context s → Path → Result Value)
    (nested : ∀ ctx : Context s, ctx.type = childType → OwnedContext p ctx → ∀ path, Successful (child ctx path))
    (path : Path) : Successful (interpretField (fieldShape ctx.type name) (tenantMeanings s p ctx name args) path child) := by
  cases ctx with
  | query =>
    cases decl with
    | project key =>
      cases found : projectOccurrence s p key with
      | none => exact ⟨.null, by simp [tenantMeanings, found, fieldShape, Context.type, interpretField]⟩
      | some row =>
        simp only [tenantMeanings, found, fieldShape, Context.type, interpretField]
        exact successful_boundary _ (nested (.project row) rfl (lookupOccurrence_owned found).1 path) true
    | projects =>
      simp only [tenantMeanings, fieldShape, Context.type, interpretField, completeList, required_propagates, List.map_map, Function.comp_def]
      apply successful_map
      refine successful_collect _ (fun ctx i => child ctx (path ++ [.index i])) 0 ?_
      intro ctx member index
      obtain ⟨row, included, rfl⟩ := List.mem_map.mp member
      exact nested (.project row) rfl (ownedOccurrences_owned included) _
  | project row =>
    cases decl with
    | tasks =>
      simp only [tenantMeanings, fieldShape, Context.type, interpretField, completeList, required_propagates, List.map_map, Function.comp_def]
      apply successful_map
      refine successful_collect _ (fun ctx i => child ctx (path ++ [.index i])) 0 ?_
      intro ctx member index
      obtain ⟨row, included, rfl⟩ := List.mem_map.mp member
      exact nested (.task row) rfl (taskOccurrences_owned included) _
  | task row =>
    cases decl with
    | taskProject =>
      obtain ⟨target, found⟩ := required row.value (List.getElem_mem _) owned
      simp only [tenantMeanings, found, fieldShape, Context.type, interpretField]
      exact successful_boundary _ (nested (.project target) rfl (lookupOccurrence_owned found).1 path) false

theorem eval_success (selection : PSelection) (ctx : Context s)
    (valid : ValidPSelection ctx.type selection) (owned : OwnedContext p ctx)
    (required : ∀ task ∈ s.tasks, task.tenant = p.tenant → ∃ row, projectOccurrence s p task.projectId = some row)
    (path : Path) : Successful (evalFields (tenantMeanings s p) selection ctx path) := by
  induction selection generalizing ctx path with
  | nil => exact ⟨[], rfl⟩
  | field name args children rest childrenIH restIH =>
    cases valid with
    | leaf decl unique tail =>
      apply successful_pair
      · cases ctx <;> cases decl <;> exact ⟨_, rfl⟩
      · exact restIH _ tail owned path
    | object decl nonempty unique nested tail =>
      apply successful_pair
      · apply object_success ctx owned decl required
        intro child same childOwned path
        apply successful_map
        exact childrenIH _ (same.symm ▸ nested) childOwned path
      · exact restIH _ tail owned path

theorem run_error_free (adapter : ExecutionBridge.ActualAdapter)
    (agreement : GraphQL.Plan.BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (selected : IR.Checked .query selection)
    (conditions : SuccessConditions request.snapshot request.principal selection) :
    ∃ fields, Runtime.run adapter request selected = ⟨.object fields, []⟩ := by
  rw [Runtime.run_eq_spec adapter agreement]
  obtain ⟨fields, result⟩ := eval_success selection (.query : Context request.snapshot) conditions.valid.2 True.intro conditions.requiredTargets []
  exact ⟨fields, by simp [EvalSpec, result, Result.map, envelope]⟩

end Example.Tenant.Success

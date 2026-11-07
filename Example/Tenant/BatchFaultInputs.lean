import Example.Tenant.S6aProofs
import GraphQL.Plan.BatchSafety

namespace Example.Tenant.BatchFault
open GraphQL GraphQL.Plan Planning Batching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evidence follows the actual preparation answers, including framework faults. -/
def PreparedEvidence (request : Binding.Request) (prepared : Batching.Prepared) : Prop :=
  Fault.Post (branchId .projects) request () () prepared.projects ∧
  ∀ i, Fault.Post (branchId .tasks) request (branchRows (carriers := Binding.carriers) .projects prepared.projects)[i] () (prepared.tasks i)

theorem post_rows_owned (field : IR.Branch parent child) (request : Binding.Request)
    (record : Binding.carriers (objectId parent)) (args : field.Args)
    (raw : Outcome ApplicationError ((branchId field).Out Binding.carriers))
    (post : Fault.Post (branchId field) request record (branchArgs field args) raw)
    (row : Binding.carriers (objectId child)) (member : row ∈ branchRows field raw) :
    Contract.ObjectInvariant request (objectId child) row := by
  rcases post with good | ⟨code, rfl⟩
  · have owned := good.2
    cases field <;> cases raw <;> simp only [branchRows] at member
    all_goals try contradiction
    · rename_i value
      cases value with
      | none => contradiction
      | some value => simp only [List.mem_singleton] at member; subst row; exact owned value rfl
    · exact owned row member
    · exact owned row member
    · simp only [List.mem_singleton] at member; subst row; exact owned
  · cases field <;> cases member

theorem prepare_contract (request : Binding.Request) :
    Sat Fault.contracts.Pre Fault.contracts.Post (Batching.prepare request) (PreparedEvidence request) := by
  unfold Batching.prepare
  constructor
  · trivial
  · intro projects valid
    apply sat_bind _ _ (sat_tabulate _ (fun i raw => Fault.Post (branchId .tasks) request
      (branchRows (carriers := Binding.carriers) .projects projects)[i] () raw) ?_)
    · intro tasks permitted; exact ⟨valid, permitted⟩
    · intro i
      exact ⟨post_rows_owned .projects request () () projects valid _ (List.getElem_mem i.isLt), fun _ proof => proof⟩

theorem prepared_row_owned (request : Binding.Request) (prepared : Batching.Prepared)
    (valid : PreparedEvidence request prepared) (index : RowIndex (rows prepared).width) :
    OwnedTask request.snapshot request.principal ((rows prepared).getValue index).1 :=
  post_rows_owned .tasks request _ () (prepared.tasks index.1) (valid.2 index.1) _ (List.getElem_mem index.2.isLt)

theorem prepared_input_pre (request : Binding.Request) (prepared : Batching.Prepared)
    (valid : PreparedEvidence request prepared) (input : Task × Unit)
    (member : input ∈ Batch.rowInputs (rows prepared)) :
    Fault.contracts.pre (branchId .taskProject) request input.1 input.2 := by
  obtain ⟨index, _, equal⟩ := List.mem_map.mp member
  subst input
  exact prepared_row_owned request prepared valid index

/-- Key equality is tied to the canonical backend agreement; declared faults
transfer unchanged, while exact answers transfer through that backend's key law. -/
theorem reuse_post (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (batch : Batch.Eligible adapter (branchId .taskProject)) (request : Binding.Request)
    (left right : Task × Unit)
    (same : batch.key.key request left.1 left.2 = batch.key.key request right.1 right.2)
    (answer : Outcome ApplicationError Project)
    (valid : Fault.Post (branchId .taskProject) request left.1 left.2 answer) :
    Fault.Post (branchId .taskProject) request right.1 right.2 answer := by
  rcases valid with ⟨exact, owned⟩ | fault
  · apply Or.inl
    refine ⟨?_, owned⟩
    have leftExpected := (Contract.tenantResolvers_satisfy_contracts adapter agreement
      (branchId .taskProject) request left.1 left.2)
    have rightExpected := (Contract.tenantResolvers_satisfy_contracts adapter agreement
      (branchId .taskProject) request right.1 right.2)
    have sameExpected : Contract.Expected (branchId .taskProject) request left.1 left.2 =
        Contract.Expected (branchId .taskProject) request right.1 right.2 := by
      have canonical field parent args := (adapter_single_agreement Binding.independentBindings adapter agreement
        2 (Binding.checked.coordinate field) request parent args)
      have eqLeft := canonical (branchId .taskProject) left.1 left.2
      have eqRight := canonical (branchId .taskProject) right.1 right.2
      have manualLeft := Contract.manual_expected (branchId .taskProject) request left.1 left.2
      have manualRight := Contract.manual_expected (branchId .taskProject) request right.1 right.2
      exact manualLeft.symm.trans (eqLeft.symm.trans ((batch.key.sufficient request _ _ _ _ same).trans (eqRight.trans manualRight)))
    exact exact.trans sameExpected
  · exact Or.inr fault

theorem wave_contract (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (batch : Batch.Eligible adapter (branchId .taskProject)) (request : Binding.Request)
    (prepared : Batching.Prepared) (valid : PreparedEvidence request prepared) (positive : 0 < capacity) :
    Sat Fault.contracts.Pre Fault.contracts.Post (Batch.rowsWave batch request (rows prepared) capacity positive)
      (fun answers => ∀ i, Fault.Post (branchId .taskProject) request ((rows prepared).getValue i).1 () (answers i)) := by
  apply Batch.rows_wave_contract Fault.contracts batch request (rows prepared) positive
    (prepared_input_pre request prepared valid) (fun _ => True.intro)
  intro left _ right _ same answer valid
  exact reuse_post adapter agreement batch request left right same answer valid

end Example.Tenant.BatchFault

import Example.Tenant.BatchFaultFrames

namespace Example.Tenant.BatchFault
open GraphQL GraphQL.Plan Planning Batching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

abbrev single (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child nested) (nonempty : nested ≠ .nil) :=
  IR.Resolved.object field args none children nonempty .nil (by simp [PSelection.names])

theorem related_ofFn (sources : List α) (values : Fin sources.length → β)
    (valid : ∀ i, relation sources[i] (values i)) : RelatedLists relation sources (List.ofFn values) := by
  induction sources with
  | nil => exact .nil
  | cons head tail ih =>
    simp only [List.ofFn_succ]
    exact .cons (valid 0) (ih (fun i => values i.succ) (fun i => valid i.succ))

/-- Parent output reconstruction reuses the original compiled frame certificate.
Children retain original coordinates, independently of shared-loading keys. -/
theorem branch_frame (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child nested) (nonempty : nested ≠ .nil)
    (request : Binding.Request) (record : Binding.carriers (objectId parent))
    (raw : Outcome ApplicationError ((branchId field).Out Binding.carriers))
    (post : Fault.Post (branchId field) request record (branchArgs field args) raw)
    (path : Spec.Path) (results : Fin (branchRows field raw).length → Spec.Result Spec.Value)
    (valid : ∀ i, FrameAt children request (branchRows field raw)[i]
      (childPath field (path ++ [.field field.name]) i.val) (results i)) :
    FrameAt (single field args children nonempty) request record path
      (assemble field raw (List.ofFn results) (path ++ [.field field.name])) := by
  intro source same owned
  subst record
  rcases Fault.exact_or_fault _ _ _ _ _ post with exact | ⟨code, exact⟩
  · subst raw
    let sources := branchRows field (meanings request.snapshot (branchId field) request.principal source (branchArgs field args))
    let convert := Binding.transport request.snapshot (objectId child)
    have rowsEq : branchRows field (Contract.Expected (branchId field) request
        (Binding.transport request.snapshot (objectId parent) source) (branchArgs field args)) = sources.map convert := by
      have transported := OutputEvidence.expected_transport request.snapshot (branchId field) request.principal source (branchArgs field args)
      change Contract.Expected (branchId field) request (Binding.transport request.snapshot (objectId parent) source) (branchArgs field args) = _ at transported
      rw [transported, branch_rows_transport]
    have lengthEq := congrArg List.length rowsEq
    simp only [List.length_map] at lengthEq
    have each : ∀ i : Fin sources.length, ∃ frame, Fault.ChildEvidence children request sources[i] frame ∧
        render (compileFor Binding.carriers Binding.Request children).output ⟨frame⟩
          (childPath field (path ++ [.field field.name]) i.val) = results ⟨i.val, by omega⟩ := by
      intro i
      apply valid ⟨i.val, by omega⟩ sources[i]
      · simp [rowsEq, convert]
      · exact Fault.source_rows_owned field request source args sources[i] (List.getElem_mem i.isLt)
    classical
    let frames := fun i => (each i).choose
    have frameEvidence : ∀ i, Fault.ChildEvidence children request sources[i] (frames i) := fun i => (each i).choose_spec.1
    have rendered : ∀ i, render (compileFor Binding.carriers Binding.Request children).output ⟨frames i⟩
        (childPath field (path ++ [.field field.name]) i.val) = results ⟨i.val, by omega⟩ := fun i => (each i).choose_spec.2
    refine ⟨objectFrame field args children nonempty request _ _ (List.ofFn frames),
      object_frame_evidence field args children nonempty request source owned _ _
        (Fault.domain_branch_evidence field args children request source owned _ (related_ofFn sources frames frameEvidence)), ?_⟩
    rw [object_frame_render]
    apply congrArg (fun values : List (Spec.Result Spec.Value) => assemble field
      (Contract.Expected (branchId field) request (Binding.transport request.snapshot (objectId parent) source) (branchArgs field args))
      values (path ++ [Spec.Segment.field field.name]))
    apply List.ext_getElem
    · simp [lengthEq]
    · intro i left right
      simpa [frames] using rendered ⟨i, by simpa using left⟩
  · subst raw
    have empty : branchRows (carriers := Binding.carriers) field (.error (.framework code)) = [] := by cases field <;> rfl
    have resultsEmpty : List.ofFn results = [] := List.eq_nil_of_length_eq_zero (by simp [empty])
    refine ⟨objectFrame field args children nonempty request _ _ [],
      object_frame_evidence field args children nonempty request source owned _ _
        (Fault.framework_branch_evidence field args children request source owned code []), ?_⟩
    rw [object_frame_render, resultsEmpty]
    rfl

end Example.Tenant.BatchFault

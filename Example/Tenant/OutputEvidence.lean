import Example.Tenant.CompiledContract
import Example.Tenant.ResponseContract

namespace Example.Tenant.OutputEvidence
open GraphQL.Plan Planning

/-- A record is related to an explicit occurrence, not an occurrence recovered by
record equality. RowsFor retains that witness at every position, including duplicates. -/
def RowFor (request : Binding.Request) (object : ObjectType)
    (source : Model request.snapshot object) (record : Binding.carriers (objectId object)) : Prop :=
  record = Binding.transport request.snapshot (objectId object) source

def RowsFor (request : Binding.Request) (object : ObjectType)
    (sources : List (Model request.snapshot object)) (records : List (Binding.carriers (objectId object))) : Prop :=
  RelatedLists (RowFor request object) sources records

theorem expected_transport (s : Snapshot) :
    MeaningTransport (Binding.transport s) (fun principal => (⟨s, principal⟩ : Binding.Request))
      (meanings s) Contract.Expected := by
  intro object field principal parent args
  exact (Contract.manual_expected field ⟨s, principal⟩ (Binding.transport s object parent) args).symm.trans
    (ExecutionBridge.adapter_transport s (Binding.adapt Binding.application) Binding.application_agreement
      field principal parent args)

theorem branch_rows_correspond (request : Binding.Request) (field : IR.Branch parent child)
    (source : Model request.snapshot parent) (args : field.Args) (error : Option Example.Tenant.FrameworkError) :
    RowsFor request child
      (branchRows field (branchCall (meanings request.snapshot) field request.principal source args error))
      (branchRows field (branchCall Contract.Expected field request
        (Binding.transport request.snapshot (objectId parent) source) args error)) := by
  have calls := branch_call_transport (Binding.transport request.snapshot)
    (fun principal => (⟨request.snapshot, principal⟩ : Binding.Request))
    (meanings request.snapshot) Contract.Expected (expected_transport request.snapshot)
    field request.principal source args error
  unfold RowsFor
  rw [calls, branch_rows_transport]
  exact forall2_mapped _ _ _ (fun _ _ => rfl)

/-- Render-level obligation, discharged for deterministic compiled frames. It takes
intermediate frame/occurrence evidence, not a premise about a final response. -/
theorem render_frame_evidence (selected : IR.Checked object selection) (request : Binding.Request)
    (source : Model request.snapshot object) (record : Binding.carriers (objectId object))
    (row : RowFor request object source record)
    (owned : Spec.OwnedContext request.principal (context request.snapshot object source))
    (frame : Frame (compileFor Binding.carriers Binding.Request selected.val).graph)
    (invariant : Contract.ExactFrame (compileFor Binding.carriers Binding.Request selected.val).graph
      (record, request, ()) frame.value) (path : Spec.Path) :
    ∃ tree, Judgment (ResponseContract.Rule request.snapshot request.principal)
      (.fields (context request.snapshot object source) selection path) tree ∧
      Spec.erase tree = render (compileFor Binding.carriers Binding.Request selected.val).output frame path := by
  have transport := compiled_transport (Binding.transport request.snapshot)
    (fun principal => (⟨request.snapshot, principal⟩ : Binding.Request)) (meanings request.snapshot)
    Contract.Expected (expected_transport request.snapshot) selected.val source request.principal path
  have semantics := (compile_for_correct selected.val (meanings request.snapshot) source request.principal path).trans
    (resolved_denotation selected.val selected.property source request.principal path)
  have valid : ValidPSelection (context request.snapshot object source).type selection := by
    rw [context_type]
    exact IR.resolved_valid selected.val
  obtain ⟨tree, authorized, erased⟩ := Spec.eval_fields_authorized selection _ valid owned path
  refine ⟨tree, ResponseContract.independent_derivation authorized, ?_⟩
  rcases frame with ⟨values⟩
  change values = _ at invariant
  subst values
  change record = _ at row
  subst record
  exact erased.trans (transport.trans semantics).symm

end Example.Tenant.OutputEvidence

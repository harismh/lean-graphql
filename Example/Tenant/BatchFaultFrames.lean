import Example.Tenant.BatchFaultInputs

namespace Example.Tenant.BatchFault
open GraphQL GraphQL.Plan Planning Batching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- Retains the original compiler's output certificate, including all paths. -/
def FrameAt (resolved : IR.Resolved object surface) (request : Binding.Request)
    (record : Binding.carriers (objectId object)) (path : Spec.Path) (result : Spec.Result Spec.Value) : Prop :=
  ∀ source : Model request.snapshot object,
    Binding.transport request.snapshot (objectId object) source = record →
    Spec.OwnedContext request.principal (context request.snapshot object source) →
    ∃ frame, Fault.ChildEvidence resolved request source frame ∧
      render (compileFor Binding.carriers Binding.Request resolved).output ⟨frame⟩ path = result

/-- Assemble a frame of the original compiled single-field selection. The proof
uses original output rendering; no alternative output semantics is introduced. -/
def objectFrame (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child nested) (nonempty : nested ≠ .nil)
    (request : Binding.Request) (record : Binding.carriers (objectId parent))
    (raw : Outcome ApplicationError ((branchId field).Out Binding.carriers))
    (frames : List (Values (compileFor Binding.carriers Binding.Request children).outputs)) :
    Values (compileFor Binding.carriers Binding.Request
      (.object field args none children nonempty .nil (by simp [PSelection.names]))).outputs :=
  (frames.map (fun frame => (⟨frame⟩ : Frame (compileFor Binding.carriers Binding.Request children).graph)),
    frames, branchRows field raw, raw, branchArgs field args, record, request, ())

theorem object_frame_render (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child nested) (nonempty : nested ≠ .nil)
    (request : Binding.Request) (record : Binding.carriers (objectId parent))
    (raw : Outcome ApplicationError ((branchId field).Out Binding.carriers)) (frames) (path : Spec.Path) :
    render (compileFor Binding.carriers Binding.Request
      (.object field args none children nonempty .nil (by simp [PSelection.names]))).output
      ⟨objectFrame field args children nonempty request record raw frames⟩ path =
    assemble field raw (frames.zipIdx.map (fun (frame, i) => render
      (compileFor Binding.carriers Binding.Request children).output ⟨frame⟩
      (childPath field (path ++ [.field field.name]) i))) (path ++ [.field field.name]) := by
  simp [objectFrame, compileFor, render, OutputRef.read, Ref.read, assemble, List.zipIdx_map, List.map_map, Function.comp_def]

theorem object_frame_evidence (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child nested) (nonempty : nested ≠ .nil)
    (request : Binding.Request) (source : Model request.snapshot parent)
    (owned : Spec.OwnedContext request.principal (context request.snapshot parent source))
    (raw : Outcome ApplicationError ((branchId field).Out Binding.carriers)) (frames)
    (evidence : Fault.BranchEvidence field args children request source raw frames) :
    Fault.ChildEvidence (.object field args none children nonempty .nil (by simp [PSelection.names])) request source
      (objectFrame field args children nonempty request (Binding.transport request.snapshot (objectId parent) source) raw frames) := by
  intro path
  obtain ⟨head, auth, erased⟩ := evidence (path ++ [.field field.name])
  refine ⟨.field field.name head .empty, .field auth (.empty owned), ?_⟩
  rw [object_frame_render]
  simp only [Spec.erase, erased, assemble, appendField_eq, Spec.objectCons]
  rfl

/-- Allows a postcondition to retain certificates for all equal record occurrences. -/
theorem sat_forall {ι : Type} [Nonempty ι] (program : Machine C A α)
    (property : ι → α → Prop) (valid : ∀ i, Sat pre post program (property i)) :
    Sat pre post program (fun result => ∀ i, property i result) := by
  induction program with
  | done => exact fun i => valid i
  | pending call resume ih =>
    constructor
    · exact (valid (Classical.choice inferInstance)).1
    · intro answer allowed
      exact ih answer (fun i => (valid i).2 answer allowed)

theorem owned_project_source (request : Binding.Request) (record : Project)
    (owned : OwnedProject request.snapshot request.principal record) :
    ∃ source : Model request.snapshot .project,
      Binding.transport request.snapshot (objectId .project) source = record ∧
      Spec.OwnedContext request.principal (context request.snapshot .project source) := by
  obtain ⟨i, bound, equal⟩ := List.mem_iff_getElem.mp owned.1
  exact ⟨⟨⟨i, bound⟩⟩, equal, by simpa [context, Spec.OwnedContext, Occurrence.value, Binding.transport, objectId] using equal ▸ owned.2⟩

theorem child_result_contract (request : Binding.Request) (child : IR.Resolved .project nested)
    (record : Project) (owned : OwnedProject request.snapshot request.principal record) (path : Spec.Path) :
    Sat Fault.contracts.Pre Fault.contracts.Post (childResult request child record path)
      (FrameAt child request record path) := by
  let Source := {source : Model request.snapshot .project // Binding.transport request.snapshot (objectId .project) source = record ∧
    Spec.OwnedContext request.principal (context request.snapshot .project source)}
  obtain ⟨source, same, valid⟩ := owned_project_source request record owned
  letI : Nonempty Source := ⟨⟨source, same, valid⟩⟩
  apply sat_weaken _ (sat_forall (ι := Source) _ (fun s result => ∃ frame, Fault.ChildEvidence child request s.val frame ∧
    render (compileFor Binding.carriers Binding.Request child).output ⟨frame⟩ path = result) ?_)
  · intro result certificate source same valid
    exact certificate ⟨source, same, valid⟩
  · intro s
    unfold childResult
    have graphSame : interpretGraph (compileFor Binding.carriers Binding.Request child).graph (record, request, ()) =
        interpretGraph (compileFor Binding.carriers Binding.Request child).graph
          (Binding.transport request.snapshot (objectId .project) s.val, request, ()) :=
      congrArg (fun record => interpretGraph (compileFor Binding.carriers Binding.Request child).graph (record, request, ())) s.property.1.symm
    rw [graphSame]
    apply sat_bind _ _ (Fault.compiled_fault_contract child request s.val s.property.2)
    intro frame certificate
    exact ⟨frame, certificate.2, rfl⟩

end Example.Tenant.BatchFault

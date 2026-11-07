import Example.Tenant.FaultOutput

namespace Example.Tenant.Fault
open GraphQL.Plan Planning

theorem source_owned_record (request : Binding.Request) (source : Model request.snapshot object)
    (owned : Spec.OwnedContext request.principal (context request.snapshot object source)) :
    Contract.ObjectInvariant request (objectId object) (Binding.transport request.snapshot (objectId object) source) := by
  cases object with
  | query => trivial
  | project => exact ⟨List.getElem_mem _, owned⟩
  | task => exact ⟨List.getElem_mem _, owned⟩

theorem source_rows_owned (field : IR.Branch parent child) (request : Binding.Request)
    (source : Model request.snapshot parent) (args : field.Args) (row : Model request.snapshot child)
    (member : row ∈ branchRows field (meanings request.snapshot (branchId field) request.principal source (branchArgs field args))) :
    Spec.OwnedContext request.principal (context request.snapshot child row) := by
  cases field with
  | project =>
    dsimp only [meanings, branchId, branchArgs, objectId] at member
    cases found : projectOccurrence request.snapshot request.principal args with
    | none => simp [branchRows, found] at member
    | some target =>
      simp only [id_eq, branchRows, found, List.mem_singleton] at member
      subst row
      exact (lookupOccurrence_owned found).1
  | projects => exact ownedOccurrences_owned member
  | tasks => exact taskOccurrences_owned member
  | taskProject =>
    dsimp only [meanings, branchId, branchArgs, objectId] at member
    cases found : projectOccurrence request.snapshot request.principal source.value.projectId with
    | none => simp [branchRows, found] at member
    | some target =>
      simp only [branchRows, found] at member
      have eq := List.mem_singleton.mp member
      subst row
      exact (lookupOccurrence_owned found).1

theorem traverse_mapped_contract (sources : List α) (convert : α → β) (execute : β → GraphQL.Machine C A γ)
    (relation : α → γ → Prop)
    (valid : ∀ source ∈ sources, Sat pre post (execute (convert source)) (relation source)) :
    Sat pre post (traverse execute (sources.map convert)) (RelatedLists relation sources) := by
  induction sources with
  | nil => exact .nil
  | cons source sources ih =>
    apply sat_bind _ _ (valid source List.mem_cons_self)
    intro value good
    apply sat_bind _ _ (ih (fun row member => valid row (List.mem_cons_of_mem _ member)))
    exact fun rest related => RelatedLists.cons good related

theorem branch_execution (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child selection) (request : Binding.Request) (source : Model request.snapshot parent)
    (owned : Spec.OwnedContext request.principal (context request.snapshot parent source))
    (raw : Outcome ApplicationError ((branchId field).Out Binding.carriers))
    (valid : raw = Contract.Expected (branchId field) request (Binding.transport request.snapshot (objectId parent) source) (branchArgs field args) ∨
      ∃ code : GraphQL.Plan.FrameworkError, raw = .error (.framework code))
    (childSafe : ∀ childSource, Spec.OwnedContext request.principal (context request.snapshot child childSource) →
      Sat contracts.Pre contracts.Post
        (interpretGraph (compileFor Binding.carriers Binding.Request children).graph
          (Binding.transport request.snapshot (objectId child) childSource, request, ()))
        (FrameEvidence children request childSource)) :
    Sat contracts.Pre contracts.Post
      (traverse (fun row => interpretGraph (compileFor Binding.carriers Binding.Request children).graph (row, request, ()))
        (branchRows field raw)) (BranchEvidence field args children request source raw) := by
  rcases valid with rfl | ⟨code, rfl⟩
  · have transport := OutputEvidence.expected_transport request.snapshot (branchId field) request.principal source (branchArgs field args)
    change Contract.Expected (branchId field) request
      (Binding.transport request.snapshot (objectId parent) source) (branchArgs field args) = _ at transport
    have rows := branch_rows_transport (Binding.transport request.snapshot) field
      (meanings request.snapshot (branchId field) request.principal source (branchArgs field args))
    have rowsEq := (congrArg (branchRows field) transport).trans rows
    rw [rowsEq]
    apply sat_weaken _ (traverse_mapped_contract _ _ _ (ChildEvidence children request) ?_)
    · exact fun frames related => domain_branch_evidence field args children request source owned frames related
    · intro childSource member
      exact sat_weaken _ (childSafe childSource (source_rows_owned field request source args childSource member)) (fun _ h => h.2)
  · have empty : branchRows (carriers := Binding.carriers) field (.error (.framework code)) = [] := by cases field <;> rfl
    rw [empty]
    exact framework_branch_evidence field args children request source owned code []

theorem compiled_fault_contract (resolved : IR.Resolved object selection) (request : Binding.Request)
    (source : Model request.snapshot object)
    (owned : Spec.OwnedContext request.principal (context request.snapshot object source)) :
    Sat contracts.Pre contracts.Post
      (interpretGraph (compileFor Binding.carriers Binding.Request resolved).graph
        (Binding.transport request.snapshot (objectId object) source, request, ()))
      (FrameEvidence resolved request source) := by
  induction resolved generalizing request with
  | nil =>
    exact ⟨identity_project _, fun _ => ⟨.empty, .empty owned, rfl⟩⟩
  | leaf field rest fresh ih =>
    simp only [compileFor, interpretGraph, interpretNode, machine_bind_assoc, GraphQL.Machine.bind]
    apply sat_bind _ _ (ih request source owned)
    intro previous good
    have tokenEq : ((compileFor Binding.carriers Binding.Request rest).graph.inputs.rename (.there .here)).read previous = request := by
      rw [renamed_read, good.1]; rfl
    have parentEq : ((compileFor Binding.carriers Binding.Request rest).graph.inputs.rename .here).read previous =
        Binding.transport request.snapshot (objectId _) source := by rw [renamed_read, good.1]; rfl
    simp only [Ref.read, tokenEq, parentEq, GraphQL.Machine.bind]
    constructor
    · simpa only [Contracts.Pre, contracts, Contract.tenant, tokenEq, parentEq] using source_owned_record request source owned
    · intro raw post
      simp only [Contracts.Post, contracts, tokenEq, parentEq] at post
      constructor
      · exact good.1
      · intro path
        obtain ⟨head, headAuth, headErase⟩ := leaf_evidence field request source owned raw post (path ++ [.field field.name])
        obtain ⟨tail, tailAuth, tailErase⟩ := good.2 path
        refine ⟨.field field.name head tail, .field headAuth tailAuth, ?_⟩
        simp only [Spec.erase, headErase, tailErase, compileFor, render, OutputRef.read, Ref.read, appendField_eq, Spec.objectCons]
        rfl
  | object field args error children nonempty rest fresh childIH restIH =>
    simp only [compileFor, interpretGraph, interpretNode, machine_bind_assoc, GraphQL.Machine.bind]
    apply sat_bind _ _ (restIH request source owned)
    intro previous good
    have tokenEq : ((compileFor Binding.carriers Binding.Request rest).graph.inputs.rename (.there .here)).read previous = request := by
      rw [renamed_read, good.1]; rfl
    have parentEq : ((compileFor Binding.carriers Binding.Request rest).graph.inputs.rename .here).read previous =
        Binding.transport request.snapshot (objectId _) source := by rw [renamed_read, good.1]; rfl
    have finish : ∀ raw, (raw = Contract.Expected (branchId field) request
        (Binding.transport request.snapshot (objectId _) source) (branchArgs field args) ∨
        ∃ code : GraphQL.Plan.FrameworkError, raw = .error (.framework code)) →
      Sat contracts.Pre contracts.Post
        ((traverse (fun row => interpretGraph (compileFor Binding.carriers Binding.Request children).graph (row, request, ()))
          (branchRows field raw)).bind (fun frames => .done
            (frames.map (fun values => (⟨values⟩ : Frame (compileFor Binding.carriers Binding.Request children).graph)),
              frames, branchRows field raw, raw, branchArgs field args, previous)))
        (FrameEvidence (.object field args error children nonempty rest fresh) request source) := by
      intro raw valid
      apply sat_bind _ _ (branch_execution field args children request source owned raw valid (fun child owned => childIH request child owned))
      intro frames evidence
      constructor
      · exact good.1
      · intro path
        obtain ⟨head, headAuth, headErase⟩ := evidence (path ++ [.field field.name])
        obtain ⟨tail, tailAuth, tailErase⟩ := good.2 path
        refine ⟨.field field.name head tail, .field headAuth tailAuth, ?_⟩
        simp only [Spec.erase, headErase, tailErase, compileFor, render, OutputRef.read, Ref.read, appendField_eq,
          List.zipIdx_map, List.map_map, Function.comp_def, Prod.map, id_eq, Spec.objectCons]
        rfl
    cases error with
    | none =>
      simp only [callNode, interpretNode, Ref.read, tokenEq, parentEq, Capture.read, GraphQL.Machine.bind]
      constructor
      · simpa only [Contracts.Pre, contracts, Contract.tenant, tokenEq, parentEq] using source_owned_record request source owned
      · intro raw post
        simp only [Contracts.Post, contracts, tokenEq, parentEq] at post
        exact finish raw (exact_or_fault _ _ _ _ _ post)
    | some code =>
      simp only [callNode, interpretNode, Ref.read, tokenEq, parentEq, Capture.read, GraphQL.Machine.bind]
      exact finish _ (Or.inr ⟨frameworkCode code, rfl⟩)

theorem execution_authorized (request : Binding.Request) (selected : IR.Checked .query selection)
    (nonempty : selection ≠ .nil) :
    Sat contracts.Pre contracts.Post (Runtime.execute request selected)
      (Spec.AuthorizedResponse request.snapshot request.principal selection) := by
  apply sat_bind _ _ (compiled_fault_contract selected.val request () True.intro)
  intro values evidence
  obtain ⟨tree, authorized, erased⟩ := evidence.2 []
  exact ⟨⟨nonempty, IR.resolved_valid selected.val⟩, tree, authorized, congrArg Spec.envelope erased⟩

theorem permitted_driver_authorized (request : Binding.Request) (selected : IR.Checked .query selection)
    (nonempty : selection ≠ .nil)
    (resolve : (call : Call schema Binding.carriers Binding.Request) → Answer ApplicationError call)
    (valid : ∀ call, contracts.Pre call → contracts.Post call (resolve call)) :
    Spec.AuthorizedResponse request.snapshot request.principal selection
      (runMachine resolve (Runtime.execute request selected)) :=
  sat_run resolve valid _ (execution_authorized request selected nonempty)

end Example.Tenant.Fault

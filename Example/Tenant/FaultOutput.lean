import Example.Tenant.FaultContracts

namespace Example.Tenant.Fault
open GraphQL.Plan Planning

theorem items_evidence (children : IR.Resolved object selection) (request : Binding.Request)
    (sources : List (Model request.snapshot object))
    (frames : List (Values (compileFor Binding.carriers Binding.Request children).outputs))
    (related : RelatedLists (ChildEvidence children request) sources frames) (path : Spec.Path) (start : Nat) :
    ∃ tree, Spec.AuthItems request.snapshot request.principal (sources.map (context request.snapshot object))
      selection path start tree ∧ Spec.erase tree =
      (Spec.collect (frames.zipIdx start |>.map (fun (values, i) =>
        render (compileFor Binding.carriers Binding.Request children).output ⟨values⟩ (path ++ [.index i])))).map Spec.Value.array := by
  induction related generalizing start with
  | nil => exact ⟨.itemsEnd, .nil, rfl⟩
  | @cons source frame sources frames head tail ih =>
    obtain ⟨headTree, authHead, eraseHead⟩ := head (path ++ [.index start])
    obtain ⟨tailTree, authTail, eraseTail⟩ := ih (start + 1)
    refine ⟨.item (.object false headTree) tailTree, .cons authHead authTail, ?_⟩
    simp only [Spec.erase, Spec.required_propagates, eraseHead, eraseTail, List.zipIdx_cons, List.map_cons, Spec.collect]
    exact Spec.array_pair _ _

def BranchEvidence (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child selection) (request : Binding.Request) (source : Model request.snapshot parent)
    (raw : Outcome ApplicationError ((branchId field).Out Binding.carriers))
    (frames : List (Values (compileFor Binding.carriers Binding.Request children).outputs)) : Prop :=
  ∀ path, ∃ tree, Spec.AuthField request.snapshot request.principal (context request.snapshot parent source)
    field.name (field.literals args) selection path tree ∧ Spec.erase tree =
    renderBranch field raw (frames.zipIdx.map (fun (values, i) =>
      render (compileFor Binding.carriers Binding.Request children).output ⟨values⟩ (childPath field path i))) path

theorem framework_branch_evidence (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child selection) (request : Binding.Request) (source : Model request.snapshot parent)
    (owned : Spec.OwnedContext request.principal (context request.snapshot parent source))
    (code : GraphQL.Plan.FrameworkError) (frames : List (Values (compileFor Binding.carriers Binding.Request children).outputs)) :
    BranchEvidence field args children request source (.error (.framework code)) frames := by
  intro path
  cases code <;> cases field <;>
    first
    | exact ⟨_, .framework (shape := .object .project true) owned rfl .argument, rfl⟩
    | exact ⟨_, .framework (shape := .list .project false false) owned rfl .argument, rfl⟩
    | exact ⟨_, .framework (shape := .list .task false false) owned rfl .argument, rfl⟩
    | exact ⟨_, .framework (shape := .object .project false) owned rfl .argument, rfl⟩
    | exact ⟨_, .framework (shape := .object .project true) owned rfl .exhausted, rfl⟩
    | exact ⟨_, .framework (shape := .list .project false false) owned rfl .exhausted, rfl⟩
    | exact ⟨_, .framework (shape := .list .task false false) owned rfl .exhausted, rfl⟩
    | exact ⟨_, .framework (shape := .object .project false) owned rfl .exhausted, rfl⟩
    | exact ⟨_, .framework (shape := .object .project true) owned rfl .internal, rfl⟩
    | exact ⟨_, .framework (shape := .list .project false false) owned rfl .internal, rfl⟩
    | exact ⟨_, .framework (shape := .list .task false false) owned rfl .internal, rfl⟩
    | exact ⟨_, .framework (shape := .object .project false) owned rfl .internal, rfl⟩

theorem domain_branch_evidence (field : IR.Branch parent child) (args : field.Args)
    (children : IR.Resolved child selection) (request : Binding.Request) (source : Model request.snapshot parent)
    (owned : Spec.OwnedContext request.principal (context request.snapshot parent source))
    (frames : List (Values (compileFor Binding.carriers Binding.Request children).outputs))
    (related : RelatedLists (ChildEvidence children request)
      (branchRows field (meanings request.snapshot (branchId field) request.principal source (branchArgs field args))) frames) :
    BranchEvidence field args children request source
      (Contract.Expected (branchId field) request (Binding.transport request.snapshot (objectId parent) source) (branchArgs field args)) frames := by
  intro path
  have transport := OutputEvidence.expected_transport request.snapshot (branchId field) request.principal source (branchArgs field args)
  change Contract.Expected (branchId field) request
    (Binding.transport request.snapshot (objectId parent) source) (branchArgs field args) = _ at transport
  rw [transport, branch_render_transport]
  cases field with
  | project =>
    dsimp only [meanings, branchId, branchArgs, objectId] at *
    cases found : projectOccurrence request.snapshot request.principal args with
    | none =>
      simp only [meanings, branchId, branchArgs, id_eq, branchRows, found] at related
      cases related
      exact ⟨.null, .rootAbsent found, by simp [Spec.erase, renderBranch, meanings, objectId, branchId, branchArgs, id_eq, found]⟩
    | some target =>
      simp only [meanings, branchId, branchArgs, id_eq, branchRows, found] at related
      cases related with
      | cons head tail =>
        cases tail
        obtain ⟨tree, auth, erased⟩ := head path
        exact ⟨.object true tree, .rootProject found auth, by
          simp [Spec.erase, renderBranch, renderSingle, meanings, objectId, branchId, branchArgs, id_eq, found,
            childPath, isList, erased]⟩
  | projects =>
    dsimp only [meanings, branchId, branchArgs, objectId] at *
    have rel : RelatedLists (ChildEvidence children request) (projectOccurrences request.snapshot request.principal) frames := related
    obtain ⟨tree, auth, erased⟩ := items_evidence children request _ frames rel path 0
    refine ⟨.list false tree, .rootProjects auth, ?_⟩
    simpa [Spec.erase, renderBranch, meanings, objectId, branchId, branchArgs, childPath, isList,
      completeRows_eq, Spec.completeList, Spec.required_propagates, Function.comp_def] using erased
  | tasks =>
    dsimp only [meanings, branchId, branchArgs, objectId] at *
    have rel : RelatedLists (ChildEvidence children request) (taskOccurrences request.snapshot request.principal source) frames := related
    obtain ⟨tree, auth, erased⟩ := items_evidence children request _ frames rel path 0
    refine ⟨.list false tree, .tasks source owned auth, ?_⟩
    simpa [Spec.erase, renderBranch, meanings, objectId, branchId, branchArgs, childPath, isList,
      completeRows_eq, Spec.completeList, Spec.required_propagates, Function.comp_def] using erased
  | taskProject =>
    dsimp only [meanings, branchId, branchArgs, objectId] at *
    cases found : projectOccurrence request.snapshot request.principal source.value.projectId with
    | none =>
      exact ⟨_, .unavailable source owned found, by
        simp [Spec.erase, renderBranch, meanings, objectId, branchId, branchArgs, id_eq, found, errorCode, isNullable]⟩
    | some target =>
      simp only [meanings, branchId, branchArgs, id_eq, branchRows, found] at related
      cases related with
      | cons head tail =>
        cases tail
        obtain ⟨tree, auth, erased⟩ := head path
        exact ⟨.object false tree, .taskProject source owned found auth, by
          simp [Spec.erase, renderBranch, renderSingle, meanings, objectId, branchId, branchArgs, id_eq, found,
            childPath, isList, erased]⟩

end Example.Tenant.Fault

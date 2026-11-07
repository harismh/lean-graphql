import Example.Tenant.Contracts

namespace Example.Tenant.Contract
open GraphQL.Plan Planning

abbrev ExactFrame (graph : Graph schema Binding.carriers Binding.Request ApplicationError inputs outputs)
    (input : Values inputs) (values : Values outputs) := values = denoteGraph Expected graph input

abbrev ExactCertificate (graph : Graph schema Binding.carriers Binding.Request ApplicationError inputs outputs)
    (input : Values inputs) := GraphProof tenant graph (fun values => values = input) (ExactFrame graph input)

theorem exact_snoc {graph : Graph schema Binding.carriers Binding.Request ApplicationError inputs outputs}
    {node : Node schema Binding.carriers Binding.Request ApplicationError outputs result}
    (prior : ExactCertificate graph input)
    (step : NodeProof tenant node (ExactFrame graph input)
      (fun _ result => result = denoteNode Expected node (denoteGraph Expected graph input))) :
    ExactCertificate (.snoc graph node) input := by
  apply GraphProof.snoc prior step
  intro values eq result resultEq
  subst values
  subst result
  rfl

theorem exact_map (f : a → b) (ref : Ref outputs a) :
    NodeProof tenant (.map f ref) (fun values => values = fixed)
      (fun _ result => result = f (ref.read fixed)) :=
  .map (fun _ eq => congrArg (fun values => f (ref.read values)) eq)

theorem exact_literal (kind : InputType) (value : kind.denote) :
    NodeProof tenant (.literal kind value) (fun values => values = fixed)
      (fun _ result => result = value) := .literal (fun _ _ => rfl)

theorem exact_call (field : FieldId schema object) (token : Ref outputs Binding.Request)
    (parent : Ref outputs (Binding.carriers object)) (args : Ref outputs field.Args)
    (owned : ObjectInvariant (token.read fixed) object (parent.read fixed)) :
    NodeProof tenant (.call field token parent args) (fun values => values = fixed)
      (fun _ result => result = Expected field (token.read fixed) (parent.read fixed) (args.read fixed)) := by
  apply NodeProof.call
  · intro values eq; subst values; exact owned
  · intro values eq result post; subst values; exact post.1

theorem related_exact (proof : RelatedLists (fun row result => result = f row) rows results) :
    results = rows.map f := by
  induction proof with
  | nil => rfl
  | cons eq _ ih => simp_all

theorem exact_each (input : Ref outputs (List a)) (captures : Capture outputs captured)
    (body : Graph schema Binding.carriers Binding.Request ApplicationError (a :: captured) childOutputs)
    (certified : ∀ row ∈ input.read fixed, ExactCertificate body (row, captures.read fixed)) :
    NodeProof tenant (.each input captures body) (fun values => values = fixed)
      (fun _ results => results = (input.read fixed).map (fun row => denoteGraph Expected body (row, captures.read fixed))) := by
  apply NodeProof.each (relation := fun _ row result => result = denoteGraph Expected body (row, captures.read fixed))
  · intro values eq row member
    subst values
    exact certified row member
  · intro values eq results related
    subst values
    exact related_exact related

theorem branch_rows_owned (field : IR.Branch parent child) (request : Binding.Request)
    (parentValue : Binding.carriers (objectId parent)) (args : field.Args)
    (error : Option Example.Tenant.FrameworkError)
    (member : row ∈ branchRows field (branchCall Expected field request parentValue args error)) :
    ObjectInvariant request (objectId child) row := by
  cases error with
  | some code => cases field <;> simp [branchCall, branchRows] at member
  | none =>
    have allowed := expected_owned (branchId field) request parentValue (branchArgs field args)
    cases field <;> simp only [branchCall] at *
    · cases found : Expected (branchId IR.Branch.project) request parentValue (branchArgs IR.Branch.project args) with
      | error e => simp [branchRows, found] at *
      | ok value =>
        cases value with
        | none => simp [branchRows, found] at *
        | some value =>
          simp only [branchRows, found] at member
          have eq := List.mem_singleton.mp member
          subst row
          rw [found] at allowed
          exact allowed value rfl
    · exact allowed row ‹_›
    · exact allowed row ‹_›
    · cases found : Expected (branchId IR.Branch.taskProject) request parentValue (branchArgs IR.Branch.taskProject args) with
      | error e => simp [branchRows, found] at *
      | ok value =>
        simp only [branchRows, found] at member
        have eq := List.mem_singleton.mp member
        subst row
        rw [found] at allowed
        exact allowed

theorem exact_branch_call (field : IR.Branch parent child) (error : Option Example.Tenant.FrameworkError)
    (token : Ref outputs Binding.Request) (row : Ref outputs (Binding.carriers (objectId parent)))
    (args : Ref outputs (branchId field).Args)
    (owned : ObjectInvariant (token.read fixed) (objectId parent) (row.read fixed)) :
    NodeProof tenant (callNode field error token row args) (fun values => values = fixed)
      (fun _ result => result = denoteNode Expected (callNode field error token row args) fixed) := by
  cases error with
  | none => exact exact_call _ _ _ _ owned
  | some code => exact exact_map _ _

/-- Exact frame equality fixes every output reference, region position and captured
request. The certificate also proves all intermediate business preconditions. -/
theorem compiled_certificate (resolved : IR.Resolved object selection)
    (parent : Binding.carriers (objectId object)) (request : Binding.Request)
    (owned : ObjectInvariant request (objectId object) parent) :
    ExactCertificate (compileFor Binding.carriers Binding.Request resolved).graph (parent, request, ()) := by
  induction resolved generalizing request with
  | nil => exact .nil (fun _ eq => eq)
  | leaf field rest fresh ih =>
    apply exact_snoc
    · exact exact_snoc (ih parent request owned) (exact_literal _ _)
    · apply exact_call
      simpa only [denoteGraph, denoteNode, Ref.read, graph_input_read] using owned
  | object field args error children nonempty rest fresh childIH restIH =>
    apply exact_snoc
    · apply exact_snoc
      · apply exact_snoc
        · apply exact_snoc
          · exact exact_snoc (restIH parent request owned) (exact_literal _ _)
          · apply exact_branch_call
            simpa only [denoteGraph, denoteNode, Ref.read, graph_input_read] using owned
        · exact exact_map _ _
      · apply exact_each
        intro row member
        simp only [denoteGraph, denoteNode, Ref.read, Capture.read, graph_input_read] at member ⊢
        apply childIH
        apply branch_rows_owned field request parent args error
        cases error <;> simpa only [callNode, branchCall, denoteNode, Ref.read, graph_input_read] using member
    · exact exact_map _ _

theorem compiled_frame_invariant (resolved : IR.Resolved object selection)
    (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter)
    (parent : Binding.carriers (objectId object)) (request : Binding.Request)
    (owned : ObjectInvariant request (objectId object) parent) :
    ExactFrame (compileFor Binding.carriers Binding.Request resolved).graph (parent, request, ())
      (denoteGraph (Adapter.meanings adapter) (compileFor Binding.carriers Binding.Request resolved).graph
        (parent, request, ())) :=
  graph_proof_sound (compiled_certificate resolved parent request owned) (Adapter.meanings adapter)
    (tenantResolvers_satisfy_contracts adapter agreement) _ rfl

end Example.Tenant.Contract

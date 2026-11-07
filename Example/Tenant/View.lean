import Example.Tenant.Execution

namespace Example.Tenant.View
open GraphQL.Plan Planning

def snapshot (s : Snapshot) (principal : Principal) : Snapshot :=
  ⟨s.projects.filter (fun row => row.tenant == principal.tenant),
    s.tasks.filter (fun row => row.tenant == principal.tenant)⟩

def request (r : Binding.Request) : Binding.Request := ⟨snapshot r.snapshot r.principal, r.principal⟩

theorem lookup_filtered (tenant : α → Nat) (id : α → String) (principal : Principal)
    (key : String) (rows : List α) :
    lookupOwned tenant id principal key (rows.filter (fun row => tenant row == principal.tenant)) =
      lookupOwned tenant id principal key rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases owned : tenant row = principal.tenant
    · simp [List.filter_cons, owned, lookupOwned, ih]
    · simp [List.filter_cons, owned, lookupOwned, ih]

theorem project_view (s : Snapshot) (p : Principal) (key : String) :
    project (snapshot s p) p key = project s p key := lookup_filtered _ _ _ _ _

theorem projects_view (s : Snapshot) (p : Principal) : projects (snapshot s p) p = projects s p := by
  simp [projects, snapshot, List.filter_filter]

theorem tasks_view (s : Snapshot) (p : Principal) (parent : Project) :
    projectTasks (snapshot s p) p parent = projectTasks s p parent := by
  simp [projectTasks, snapshot, lookup_filtered]

theorem expected_view (field : FieldId schema object) (r : Binding.Request)
    (parent : Binding.carriers object) (args : field.Args) :
    Contract.Expected field (request r) parent args = Contract.Expected field r parent args := by
  rcases object with ⟨object, bound⟩
  rcases field with ⟨⟨field, valid⟩⟩
  rcases object with _ | (_ | (_ | object)) <;>
    rcases field with _ | (_ | (_ | field)) <;>
    try { simp [schema] at bound valid <;> omega }
  · exact congrArg Except.ok (project_view r.snapshot r.principal args)
  · exact congrArg Except.ok (projects_view r.snapshot r.principal)
  · rfl
  · rfl
  · exact congrArg Except.ok (tasks_view r.snapshot r.principal parent)
  · rfl
  · rfl
  · exact congrArg (fun found => match found with
      | some row => (Except.ok row : Outcome ApplicationError Project)
      | none => Except.error (.application .unavailable)) (project_view r.snapshot r.principal parent.projectId)

theorem view_transport : MeaningTransport (fun _ value => value) request Contract.Expected Contract.Expected := by
  intro object field r parent args
  apply (expected_view field r parent args).trans
  exact (convert_outcome_identity field.decl.output (Contract.Expected field r parent args)).symm

theorem run_expected (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter) (r : Binding.Request)
    (selected : IR.Checked .query selection) :
    Runtime.run adapter r selected =
      Spec.envelope (operationDenotes Contract.Expected (compileFor Binding.carriers Binding.Request selected.val) () r []) := by
  apply (Runtime.run_eq_plan adapter r selected).trans
  exact congrArg (fun values => Spec.envelope (render
    (compileFor Binding.carriers Binding.Request selected.val).output ⟨values⟩ []))
    (Contract.compiled_frame_invariant selected.val adapter agreement () r True.intro)

/-- Modeled response noninterference, including errors and ordering. This concerns
pure record data, not timing, backend traces, external services, or shared caches. -/
theorem run_tenant_view (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter) (r : Binding.Request)
    (selected : IR.Checked .query selection) :
    Runtime.run adapter (request r) selected = Runtime.run adapter r selected := by
  rw [run_expected adapter agreement, run_expected adapter agreement]
  exact congrArg Spec.envelope (compiled_transport (fun _ value => value) request
    Contract.Expected Contract.Expected view_transport selected.val () r [])

end Example.Tenant.View

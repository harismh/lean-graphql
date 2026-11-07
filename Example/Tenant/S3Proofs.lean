import Example.Tenant.S2Proofs
import Example.Tenant.ResponseContract
import Example.Tenant.CompiledContract
import Example.Tenant.OutputEvidence
import GraphQL.Plan.BoundedExample

namespace Example.Tenant.S3Proofs
open GraphQL.Plan

def request : Binding.Request := ⟨Checks.snapshot, Checks.caller⟩

theorem removed_ownership_guard_rejected :
    ¬ Contract.tenant.post Binding.rootProject request () "shared" (.ok (some Checks.foreignProject)) := by
  intro h
  have bad := h.2 Checks.foreignProject rfl
  have owned : Checks.foreignProject.tenant = Checks.caller.tenant := bad.2
  contradiction

theorem swapped_scalar_rejected :
    ¬ Contract.tenant.post Binding.projectTitle request Checks.ownedProject () (.ok Checks.ownedProject.id) := by
  intro h
  have eq : Checks.ownedProject.id = Checks.ownedProject.title := Except.ok.inj h.1
  contradiction

theorem unexpected_error_rejected :
    ¬ Contract.tenant.post Binding.taskProject request Checks.ownedTask () (.error (.framework .internal)) := by
  intro h
  have bad : (GraphQL.Plan.PublicError.framework .internal : GraphQL.Plan.PublicError ApplicationError) =
      .application .unavailable := h.2
  contradiction

theorem manual_contract_bundle : BackendSatisfies Contract.tenant (Adapter.meanings (Binding.adapt Binding.application)) :=
  Contract.tenantResolvers_satisfy_contracts _ Binding.application_agreement

/-- Non-root records do not gain a valid call precondition from their Lean type. -/
theorem foreign_parent_rejected : ¬ Contract.tenant.pre Binding.projectTitle request Checks.foreignProject () := by
  intro h
  have bad : Checks.foreignProject.tenant = Checks.caller.tenant := h.2
  contradiction

theorem response_rule_example : ResponseContract.Satisfies Checks.snapshot Checks.caller
    (.field "projects" [] (.field "id" [] .nil .nil) .nil)
    (Spec.envelope (Spec.erase (.field "projects" (.failure false (.framework .exhausted) [.field "projects"]) .empty))) := by
  constructor
  · exact ⟨by decide, .object .projects (by decide) (by simp [PSelection.names])
      (.leaf .projectId (by simp [PSelection.names]) .nil) .nil⟩
  · refine ⟨_, .step _ ?_ ResponseContract.Rule.field, rfl⟩
    intro pair member
    rcases List.mem_cons.mp member with eq | member
    · subst pair
      exact .step [] (by simp) (.framework (ctx := .query) (shape := .list .project false false) True.intro rfl .exhausted)
    · have eq := List.mem_singleton.mp member
      subst pair
      exact .step [] (by simp) (.empty True.intro)

def titleGraph : Graph Planning.schema Binding.carriers Binding.Request ApplicationError
    [Project, Binding.Request, Unit] [Outcome ApplicationError String, Project, Binding.Request, Unit] :=
  .snoc .nil (.call Binding.projectTitle (.there .here) .here (.there (.there .here)))

theorem title_graph_certificate : GraphProof Contract.tenant titleGraph
    (fun values => OwnedProject values.2.1.snapshot values.2.1.principal values.1)
    (fun values => values.1 = .ok values.2.1.title) := by
  apply GraphProof.snoc (.nil (fun _ h => h))
    (NodeProof.call (fun _ h => h) (fun _ _ _ h => h))
  intro values _ result post
  exact post.1

theorem title_graph_behavior (adapter : ExecutionBridge.ActualAdapter)
    (agreement : BindingAgreement Binding.independentBindings adapter)
    (request : Binding.Request) (parent : Project)
    (owned : OwnedProject request.snapshot request.principal parent) :
    (denoteGraph (Adapter.meanings adapter) titleGraph (parent, request, (), ())).1 = .ok parent.title :=
  graph_proof_sound title_graph_certificate (Adapter.meanings adapter)
    (Contract.tenantResolvers_satisfy_contracts adapter agreement) _ owned

theorem foreign_call_uncertifiable :
    ¬ NodeProof Contract.tenant
      (Node.call Binding.projectTitle (.there .here) .here (.there (.there .here)) :
        Node Planning.schema Binding.carriers Binding.Request ApplicationError
          [Project, Binding.Request, Unit] (Outcome ApplicationError String))
      (fun _ => True) (fun _ _ => True) := by
  intro certificate
  have ready := node_certificate_ready certificate
  exact foreign_parent_rejected (ready (Checks.foreignProject, request, (), ()) True.intro)

def unguardedAdapter : ExecutionBridge.ActualAdapter := Binding.adapt
  { Binding.application with queryProject := ⟨fun request _ key =>
      .ok (request.snapshot.projects.find? (fun row => row.id == key)), none⟩ }

theorem unguarded_backend_rejected : ¬ BackendSatisfies Contract.tenant (Adapter.meanings unguardedAdapter) := by
  intro satisfies
  have post := satisfies Binding.rootProject request () "shared" True.intro
  exact removed_ownership_guard_rejected post

def titleResultSpec (parent : Project) : ResultSpec Spec.Error Spec.Value :=
  ⟨fun value => value = .string parent.title, fun _ => False⟩

theorem title_completion_contract (request : Binding.Request) (parent : Project)
    (raw : Outcome ApplicationError String)
    (post : Contract.tenant.post Binding.projectTitle request parent () raw) (path : Spec.Path) :
    (titleResultSpec parent).Satisfies (Spec.toCompletion (Planning.renderLeaf (carriers := Binding.carriers) IR.Leaf.projectTitle raw path)) := by
  have eq : raw = .ok parent.title := post.1
  subst raw
  exact result_leaf (titleResultSpec parent) _ rfl

end Example.Tenant.S3Proofs

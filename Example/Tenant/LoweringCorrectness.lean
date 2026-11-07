import Example.Tenant.Compile
import Example.Tenant.Template
import Example.Tenant.ShapeConsistency

namespace Example.Tenant.Planning

theorem resolved_denotation (resolved : IR.Resolved object selection) (clean : IR.Clean resolved)
    (parent : Model s object) (principal : Principal) (path : Spec.Path) :
    denoteResolved (meanings s) resolved parent principal path =
      (Spec.evalFields (Spec.tenantMeanings s principal) selection (context s object parent) path).map
        Spec.Value.object := by
  induction resolved generalizing principal path with
  | nil => rfl
  | leaf field rest fresh ih =>
    simp only [IR.Clean] at clean
    simp only [denoteResolved, ih clean, appendField_eq, Spec.object_pair, Spec.evalFields]
    cases field <;> rfl
  | object field args error children nonempty rest fresh childIH restIH =>
    obtain ⟨rfl, hc, hr⟩ := clean
    simp only [denoteResolved, restIH hr, appendField_eq, Spec.object_pair, Spec.evalFields]
    congr 2
    simp only [branchCall]
    cases field with
    | project =>
      have callEq : meanings s (branchId .project) principal parent (branchArgs .project args) =
          .ok (projectOccurrence s principal args) := rfl
      rw [callEq]
      change _ = Spec.interpretField (some (.object .project true))
        (match projectOccurrence s principal args with | none => .absent | some r => .object (.project r)) _ _
      change renderBranch (carriers := models s) .project (.ok (projectOccurrence s principal args)) _ _ = _
      cases found : projectOccurrence s principal args <;>
        simp [objectId, meanings, branchId, branchArgs, branchRows, renderBranch, renderSingle,
          IR.Branch.name, IR.Branch.literals, context, Spec.Context.type, Spec.fieldShape,
          Spec.tenantMeanings, Spec.interpretField, found, childPath, isList, childIH hc, List.zipIdx_cons, List.zipIdx_nil, Spec.Shape.nullable] <;> rfl
    | projects =>
      have callEq : meanings s (branchId .projects) principal parent (branchArgs .projects args) =
          .ok (projectOccurrences s principal) := rfl
      rw [callEq]
      change renderBranch (carriers := models s) .projects (.ok (projectOccurrences s principal)) _ _ =
        Spec.interpretField (some (.list .project false false))
          (.objects ((projectOccurrences s principal).map Spec.Context.project)) _ _
      simp [objectId, meanings, branchId, branchArgs, branchRows, renderBranch, completeRows_eq,
        IR.Branch.name, IR.Branch.literals, context, Spec.Context.type, Spec.fieldShape,
        Spec.tenantMeanings, Spec.interpretField, childPath, isList, childIH hc,
        List.zipIdx_map, List.map_map, Function.comp_def] <;> rfl
    | tasks =>
      change renderBranch (carriers := models s) .tasks (.ok (taskOccurrences s principal parent)) _ _ =
        Spec.interpretField (some (.list .task false false))
          (.objects ((taskOccurrences s principal parent).map Spec.Context.task)) _ _
      simp [objectId, meanings, branchId, branchArgs, branchRows, renderBranch, completeRows_eq,
        IR.Branch.name, IR.Branch.literals, context, Spec.Context.type, Spec.fieldShape,
        Spec.tenantMeanings, Spec.interpretField, childPath, isList, childIH hc,
        List.zipIdx_map, List.map_map, Function.comp_def] <;> rfl
    | taskProject =>
      change renderBranch (carriers := models s) .taskProject
        (match projectOccurrence s principal parent.value.projectId with
          | some r => .ok r | none => .error (.application .unavailable)) _ _ =
        Spec.interpretField (some (.object .project false))
          (match projectOccurrence s principal parent.value.projectId with
            | none => .unavailable | some r => .object (.project r)) _ _
      cases found : projectOccurrence s principal parent.value.projectId <;>
        simp [objectId, meanings, branchId, branchArgs, branchRows, renderBranch, renderSingle,
          IR.Branch.name, IR.Branch.literals, context, Spec.Context.type, Spec.fieldShape,
          Spec.tenantMeanings, Spec.interpretField, found, childPath, isList, isNullable,
          errorCode, childIH hc, List.zipIdx_cons, List.zipIdx_nil, Spec.Shape.nullable] <;> rfl

/-- The paired plan's pure response, without the production executor. -/
def plannedResponse (s : Snapshot) (p : Principal) (selected : IR.Checked .query selection) : Spec.Response :=
  Spec.envelope (operationDenotes (meanings s) (compile s selected.val) () p [])

theorem planned_response_eq (selected : IR.Checked .query selection) :
    plannedResponse s p selected = Spec.EvalSpec (Spec.tenantMeanings s p) selection := by
  unfold plannedResponse
  rw [compile_correct, resolved_denotation selected.val selected.property]
  rfl

theorem planned_authorized (selected : IR.Checked .query selection) (nonempty : selection ≠ .nil) :
    Spec.AuthorizedResponse s p selection (plannedResponse s p selected) := by
  rw [planned_response_eq]
  exact Spec.eval_authorized ⟨nonempty, IR.resolved_valid selected.val⟩

theorem planned_conforms (selected : IR.Checked .query selection) (nonempty : selection ≠ .nil) :
    Spec.Conforms selection (plannedResponse s p selected) := by
  rw [planned_response_eq]
  exact Spec.eval_conforms ⟨nonempty, IR.resolved_valid selected.val⟩

def prepare (s : Snapshot) (template : IR.Template .query) : Option (Operation s .query) :=
  match IR.instantiateP1 template with
  | none => none
  | some selected => if selected.1 = .nil then none else some (compile s selected.2.val)

theorem prepare_correct (template : IR.Template .query) (operation : Operation s .query)
    (h : prepare s template = some operation) :
    ∃ selection, template.surfaceP1 = some selection ∧ ValidOperation selection ∧
      Spec.envelope (operationDenotes (meanings s) operation () p []) =
        Spec.EvalSpec (Spec.tenantMeanings s p) selection := by
  unfold prepare at h
  cases hi : IR.instantiateP1 template with
  | none => simp [hi] at h
  | some selected =>
    simp only [hi, Option.bind_some] at h
    split at h
    · contradiction
    · rename_i ne
      cases h
      exact ⟨selected.1, IR.instantiate_source template selected hi,
        ⟨ne, IR.resolved_valid selected.2.val⟩, planned_response_eq selected.2⟩

end Example.Tenant.Planning

import Example.Tenant.Instantiate

namespace Example.Tenant.Preparation
open GraphQL.Plan Planning
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def parameterMeanings (s : Snapshot) (key : Except InputCoercion.Error String) : Meanings schema (models s) Principal ApplicationError :=
  fun {object} field principal parent args =>
    match object, field with
    | ⟨0, _⟩, ⟨⟨0, _⟩⟩ => match key with | .ok value => .ok (projectOccurrence s principal value) | .error _ => .error (.framework .argument)
    | ⟨0, _⟩, ⟨⟨1, _⟩⟩ => .ok (projectOccurrences s principal)
    | ⟨0, _⟩, ⟨⟨n + 2, h⟩⟩ => False.elim (by simp [schema] at h; omega)
    | ⟨1, _⟩, ⟨⟨0, _⟩⟩ => .ok parent.value.id
    | ⟨1, _⟩, ⟨⟨1, _⟩⟩ => .ok parent.value.title
    | ⟨1, _⟩, ⟨⟨2, _⟩⟩ => .ok (taskOccurrences s principal parent)
    | ⟨1, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [schema] at h; omega)
    | ⟨2, _⟩, ⟨⟨0, _⟩⟩ => .ok parent.value.id
    | ⟨2, _⟩, ⟨⟨1, _⟩⟩ => .ok parent.value.title
    | ⟨2, _⟩, ⟨⟨2, _⟩⟩ => match projectOccurrence s principal parent.value.projectId with
        | some row => .ok row | none => .error (.application .unavailable)
    | ⟨2, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [schema] at h; omega)
    | ⟨n + 3, h⟩, _ => False.elim (by simp [schema] at h; omega)


theorem instantiated_denotation (source : IR.Resolved object surface) (clean : IR.Clean source)
    (key : Except InputCoercion.Error String) (parent : Model snapshot object) (principal : Principal) (path : Spec.Path) :
    denoteResolved (meanings snapshot) (instantiate key source clean).resolved parent principal path =
      denoteResolved (parameterMeanings snapshot key) source parent principal path := by
  induction source generalizing principal path with
  | nil => rfl
  | leaf field rest fresh ih =>
    simp only [instantiate, denoteResolved, ih]
    cases field <;> rfl
  | object field args error children nonempty rest fresh childIH restIH =>
    obtain ⟨rfl, hc, hr⟩ := clean
    cases field <;> cases key <;>
      simp [instantiate, denoteResolved, keyValue, keyError, branchCall, branchArgs, branchId,
        meanings, parameterMeanings, branchRows, objectId, childIH hc, restIH hr] <;> rfl

theorem parameter_denotation (resolved : IR.Resolved object selection) (clean : IR.Clean resolved) (key : Except InputCoercion.Error String)
    (parent : Model s object) (principal : Principal) (path : Spec.Path) :
    denoteResolved (parameterMeanings s key) resolved parent principal path =
      (Spec.evalFields (InputSurface.meanings s principal key) selection (context s object parent) path).map
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
      cases key with
      | error code =>
        have callEq : parameterMeanings s (.error code) (branchId .project) principal parent (branchArgs .project args) =
            .error (.framework .argument) := rfl
        rw [callEq]
        rfl
      | ok value =>
        have callEq : parameterMeanings s (.ok value) (branchId .project) principal parent (branchArgs .project args) =
            .ok (projectOccurrence s principal value) := rfl
        rw [callEq]
        change _ = Spec.interpretField (some (.object .project true))
          (match projectOccurrence s principal value with | none => .absent | some r => .object (.project r)) _ _
        change renderBranch (carriers := models s) .project (.ok (projectOccurrence s principal value)) _ _ = _
        cases found : projectOccurrence s principal value <;>
          simp [objectId, parameterMeanings, branchId, branchArgs, branchRows, renderBranch, renderSingle,
            IR.Branch.name, IR.Branch.literals, context, Spec.Context.type, Spec.fieldShape,
            InputSurface.meanings, Spec.tenantMeanings, Spec.interpretField, found, childPath, isList, childIH hc, List.zipIdx_cons, List.zipIdx_nil, Spec.Shape.nullable] <;> rfl
    | projects =>
      have callEq : parameterMeanings s key (branchId .projects) principal parent (branchArgs .projects args) =
          .ok (projectOccurrences s principal) := rfl
      rw [callEq]
      change renderBranch (carriers := models s) .projects (.ok (projectOccurrences s principal)) _ _ =
        Spec.interpretField (some (.list .project false false))
          (.objects ((projectOccurrences s principal).map Spec.Context.project)) _ _
      simp [objectId, parameterMeanings, branchId, branchArgs, branchRows, renderBranch, completeRows_eq,
        IR.Branch.name, IR.Branch.literals, context, Spec.Context.type, Spec.fieldShape,
        InputSurface.meanings, Spec.tenantMeanings, Spec.interpretField, childPath, isList, childIH hc,
        List.zipIdx_map, List.map_map, Function.comp_def] <;> rfl
    | tasks =>
      change renderBranch (carriers := models s) .tasks (.ok (taskOccurrences s principal parent)) _ _ =
        Spec.interpretField (some (.list .task false false))
          (.objects ((taskOccurrences s principal parent).map Spec.Context.task)) _ _
      simp [objectId, parameterMeanings, branchId, branchArgs, branchRows, renderBranch, completeRows_eq,
        IR.Branch.name, IR.Branch.literals, context, Spec.Context.type, Spec.fieldShape,
        InputSurface.meanings, Spec.tenantMeanings, Spec.interpretField, childPath, isList, childIH hc,
        List.zipIdx_map, List.map_map, Function.comp_def] <;> rfl
    | taskProject =>
      change renderBranch (carriers := models s) .taskProject
        (match projectOccurrence s principal parent.value.projectId with
          | some r => .ok r | none => .error (.application .unavailable)) _ _ =
        Spec.interpretField (some (.object .project false))
          (match projectOccurrence s principal parent.value.projectId with
            | none => .unavailable | some r => .object (.project r)) _ _
      cases found : projectOccurrence s principal parent.value.projectId <;>
        simp [objectId, parameterMeanings, branchId, branchArgs, branchRows, renderBranch, renderSingle,
          IR.Branch.name, IR.Branch.literals, context, Spec.Context.type, Spec.fieldShape,
          InputSurface.meanings, Spec.tenantMeanings, Spec.interpretField, found, childPath, isList, isNullable,
          errorCode, childIH hc, List.zipIdx_cons, List.zipIdx_nil, Spec.Shape.nullable] <;> rfl


end Example.Tenant.Preparation

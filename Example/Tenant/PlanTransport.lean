import Example.Tenant.Compile
import GraphQL.Plan.Conversion

namespace Example.Tenant.Planning
open GraphQL.Plan

variable {source target : Fin 3 → Type} {sourceScope targetScope : Type}

/-- Natural field semantics under carrier and request-context conversion. -/
def MeaningTransport (convert : ∀ object, source object → target object)
    (scopeMap : sourceScope → targetScope)
    (before : Meanings schema source sourceScope ApplicationError)
    (after : Meanings schema target targetScope ApplicationError) : Prop :=
  ∀ {object} (field : FieldId schema object) token parent args,
    after field (scopeMap token) (convert object parent) args =
      convertOutcome field.decl.output convert (before field token parent args)

theorem leaf_transport (convert : ∀ object, source object → target object)
    (field : IR.Leaf object) (raw : Outcome ApplicationError ((leafId field).Out source)) (path : Spec.Path) :
    renderLeaf field (convertOutcome (leafId field).decl.output convert raw) path = renderLeaf field raw path := by
  cases field <;> cases raw <;> rfl

theorem branch_rows_transport (convert : ∀ object, source object → target object)
    (field : IR.Branch parent child) (raw : Outcome ApplicationError ((branchId field).Out source)) :
    branchRows field (convertOutcome (branchId field).decl.output convert raw) =
      (branchRows field raw).map (convert (objectId child)) := by
  cases field <;> cases raw with
  | error error => rfl
  | ok value => first | rfl | (cases value <;> rfl)

theorem branch_render_transport (convert : ∀ object, source object → target object)
    (field : IR.Branch parent child) (raw : Outcome ApplicationError ((branchId field).Out source))
    (completed : List (Spec.Result Spec.Value)) (path : Spec.Path) :
    renderBranch field (convertOutcome (branchId field).decl.output convert raw) completed path =
      renderBranch field raw completed path := by
  cases field <;> cases raw with
  | error error => rfl
  | ok value => first | rfl | (cases value <;> rfl)

theorem branch_call_transport (convert : ∀ object, source object → target object)
    (scopeMap : sourceScope → targetScope) (before : Meanings schema source sourceScope ApplicationError)
    (after : Meanings schema target targetScope ApplicationError) (h : MeaningTransport convert scopeMap before after)
    (field : IR.Branch parent child) (token : sourceScope) (row : source (objectId parent))
    (args : field.Args) (error : Option FrameworkError) :
    branchCall after field (scopeMap token) (convert _ row) args error =
      convertOutcome (branchId field).decl.output convert (branchCall before field token row args error) := by
  cases error with
  | none => exact h _ _ _ _
  | some error => rfl

theorem resolved_transport (convert : ∀ object, source object → target object)
    (scopeMap : sourceScope → targetScope) (before : Meanings schema source sourceScope ApplicationError)
    (after : Meanings schema target targetScope ApplicationError) (h : MeaningTransport convert scopeMap before after)
    (resolved : IR.Resolved object selection) (row : source (objectId object))
    (token : sourceScope) (path : Spec.Path) :
    denoteResolved after resolved (convert _ row) (scopeMap token) path =
      denoteResolved before resolved row token path := by
  unfold MeaningTransport at h
  induction resolved generalizing token path with
  | nil => rfl
  | leaf field rest fresh ih =>
    simp only [denoteResolved, h, leaf_transport, ih]
  | object field args error children nonempty rest fresh childIH restIH =>
    simp only [denoteResolved, branch_call_transport convert scopeMap before after h,
      branch_rows_transport, List.zipIdx_map, List.map_map, Function.comp_def, childIH,
      branch_render_transport, restIH, Prod.map, id_eq]

theorem compiled_transport (convert : ∀ object, source object → target object)
    (scopeMap : sourceScope → targetScope) (before : Meanings schema source sourceScope ApplicationError)
    (after : Meanings schema target targetScope ApplicationError) (h : MeaningTransport convert scopeMap before after)
    (resolved : IR.Resolved object selection) (row : source (objectId object))
    (token : sourceScope) (path : Spec.Path) :
    operationDenotes after (compileFor target targetScope resolved) (convert _ row) (scopeMap token) path =
      operationDenotes before (compileFor source sourceScope resolved) row token path := by
  rw [compile_for_correct, compile_for_correct]
  exact resolved_transport convert scopeMap before after h resolved row token path

end Example.Tenant.Planning

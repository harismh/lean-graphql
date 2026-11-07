import Example.Tenant.Consistency

namespace Example.Tenant.Spec

/-- A completed value has its promised shape; a bubbling result has a real error. -/
def Good (P : α → Prop) : Result α → Prop
  | .ok value _ => P value
  | .bubble errors => errors ≠ []

theorem good_map (h : Good P r) (preserves : ∀ x, P x → Q (f x)) : Good Q (r.map f) := by
  cases r <;> simp_all [Good, Result.map]

theorem good_pair (ha : Good P a) (hb : Good Q b)
    (preserves : ∀ x y, P x → Q y → R (f x y)) : Good R (pair f a b) := by
  cases a <;> cases b <;> simp_all [Good, pair, Result.errors]

theorem good_boundary (h : Good P r) (nullAllowed : n = true → P .null) :
    Good P (boundary n r) := by
  cases r <;> cases n <;> simp_all [Good, boundary]

theorem good_failure (shape : Shape) (code : PublicError ApplicationError) (path : Path) :
    Good (ValueConforms shape children) (fail shape.nullable code path) := by
  apply good_boundary
  · simp [Good]
  · exact fun h => .null h

theorem good_object (h : Good (ObjectConforms type selection) fields) (n : Bool) :
    Good (ValueConforms (.object type n) selection) (boundary n (fields.map Value.object)) := by
  apply good_boundary (good_map h (fun _ proof => .object proof))
  exact fun hn => .null hn

theorem good_items (rows : List (Context s))
    (child : Context s → Path → Result (List (String × Value)))
    (each : ∀ ctx ∈ rows, ∀ path, Good (ObjectConforms type selection) (child ctx path))
    (path : Path) (start : Nat) :
    Good (ItemsConform type false selection)
      (collect (rows.zipIdx start |>.map
        (fun (ctx, i) => (child ctx (path ++ [.index i])).map Value.object))) := by
  induction rows generalizing start with
  | nil => exact .nil
  | cons ctx rest ih =>
    simp only [List.zipIdx_cons, List.map_cons, collect]
    have head : Good (ValueConforms (.object type false) selection)
        ((child ctx (path ++ [.index start])).map Value.object) :=
      good_map (each ctx List.mem_cons_self _) (fun _ proof => .object proof)
    apply good_pair head (ih (fun c hc => each c (List.mem_cons_of_mem _ hc)) (start + 1))
    exact fun _ _ head tail => .cons head tail

theorem good_list (rows : List (Context s))
    (child : Context s → Path → Result (List (String × Value)))
    (each : ∀ ctx ∈ rows, ∀ path, Good (ObjectConforms type selection) (child ctx path))
    (path : Path) :
    Good (ValueConforms (.list type false false) selection)
      (completeList false false (rows.zipIdx.map
        (fun (ctx, i) => (child ctx (path ++ [.index i])).map Value.object))) := by
  simp only [completeList, required_propagates]
  simp only [List.map_map, Function.comp_def, required_propagates]
  exact good_map (good_items rows child each path 0) (fun _ h => .list h)

theorem leaf_shape (ctx : Context s) (decl : LeafField ctx.type name) (path : Path) :
    Good (ValueConforms (.scalar false) .nil)
      (interpretField (fieldShape ctx.type name) (tenantMeanings s p ctx name []) path
        (fun child atPath => (evalFields (tenantMeanings s p) .nil child atPath).map Value.object)) := by
  cases ctx <;> cases decl <;> exact .scalar

theorem object_shape (ctx : Context s) (decl : ObjectField ctx.type name args childType)
    (selection : PSelection)
    (nested : ∀ child : Context s, child.type = childType → ∀ path,
      Good (ObjectConforms childType selection) (evalFields (tenantMeanings s p) selection child path))
    (path : Path) :
    ∃ shape, fieldShape ctx.type name = some shape ∧
      Good (ValueConforms shape selection)
        (interpretField (fieldShape ctx.type name) (tenantMeanings s p ctx name args) path
          (fun child atPath => (evalFields (tenantMeanings s p) selection child atPath).map Value.object)) := by
  cases ctx with
  | query =>
    cases decl with
    | project key =>
      refine ⟨.object .project true, rfl, ?_⟩
      cases found : projectOccurrence s p key with
      | none =>
        simp only [fieldShape, Context.type, tenantMeanings, found, interpretField, Good]
        exact .null rfl
      | some r =>
        simp only [fieldShape, Context.type, tenantMeanings, found, interpretField]
        exact good_object (nested (.project r) rfl path) true
    | projects =>
      refine ⟨.list .project false false, rfl, ?_⟩
      apply good_list _ _ _ path
      intro ctx member
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp member
      exact nested (.project r) rfl
  | project r =>
    cases decl with
    | tasks =>
      refine ⟨.list .task false false, rfl, ?_⟩
      apply good_list _ _ _ path
      intro ctx member
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp member
      exact nested (.task r) rfl
  | task r =>
    cases decl with
    | taskProject =>
      refine ⟨.object .project false, rfl, ?_⟩
      cases found : projectOccurrence s p r.value.projectId with
      | none =>
        simp only [fieldShape, Context.type, tenantMeanings, found, interpretField]
        exact good_failure _ _ _
      | some target =>
        simp only [fieldShape, Context.type, tenantMeanings, found, interpretField]
        exact good_object (nested (.project target) rfl path) false

theorem eval_fields_conform (selection : PSelection) (ctx : Context s)
    (valid : ValidPSelection ctx.type selection) (path : Path) :
    Good (ObjectConforms ctx.type selection) (evalFields (tenantMeanings s p) selection ctx path) := by
  induction selection generalizing ctx path with
  | nil => exact .nil
  | field name args children rest childrenIH restIH =>
    cases valid with
    | leaf decl unique tail =>
      simp only [evalFields]
      apply good_pair (leaf_shape (p := p) ctx decl (path ++ [Segment.field name])) (restIH ctx tail path)
      exact fun _ _ head tail => .cons (leaf_declaration_has_shape decl) head tail
    | object decl nonempty unique nested tail =>
      obtain ⟨shape, hs, headGood⟩ := object_shape ctx decl children
        (fun child same path => by
          simpa [same] using childrenIH child (same ▸ nested) path) (path ++ [.field name])
      apply good_pair headGood (restIH ctx tail path)
      exact fun _ _ head tail => .cons hs head tail

theorem eval_conforms (valid : ValidOperation selection) :
    Conforms selection (EvalSpec (tenantMeanings s p) selection) := by
  have good := eval_fields_conform (s := s) (p := p) selection .query valid.2 []
  refine ⟨valid, ?_⟩
  unfold EvalSpec
  cases h : evalFields (tenantMeanings s p) selection .query [] <;>
    simpa [h, Good, Result.map, envelope, Context.type] using good

end Example.Tenant.Spec

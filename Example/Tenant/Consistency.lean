import Example.Tenant.Authorization
import Example.Tenant.Conformance

namespace Example.Tenant.Spec

def objectCons (name : String) (v rest : Value) : Value :=
  match rest with | .object fields => .object ((name, v) :: fields) | _ => .null
def arrayCons (v rest : Value) : Value :=
  match rest with | .array values => .array (v :: values) | _ => .null

theorem object_pair (name : String) (a : Result Value) (b : Result (List (String × Value))) :
    pair (objectCons name) a (b.map Value.object) =
      (pair (fun v fs => (name, v) :: fs) a b).map Value.object := by
  cases a <;> cases b <;> rfl

theorem array_pair (a : Result Value) (b : Result (List Value)) :
    pair arrayCons a (b.map Value.array) = (pair List.cons a b).map Value.array := by
  cases a <;> cases b <;> rfl

theorem authorize_items (rows : List (Context s)) (selection : PSelection)
    (child : Context s → Path → Result Value)
    (witness : ∀ ctx ∈ rows, ∀ path, ∃ tree,
      AuthTree s p ctx selection path tree ∧ erase tree = child ctx path)
    (path : Path) (start : Nat) :
    ∃ tree, AuthItems s p rows selection path start tree ∧
      erase tree = (collect (rows.zipIdx start |>.map
        (fun (ctx, i) => child ctx (path ++ [.index i])))).map Value.array := by
  induction rows generalizing start with
  | nil => exact ⟨.itemsEnd, .nil, rfl⟩
  | cons ctx rest ih =>
    obtain ⟨head, hh, he⟩ := witness ctx List.mem_cons_self (path ++ [.index start])
    obtain ⟨tail, ht, te⟩ := ih (fun r hr => witness r (List.mem_cons_of_mem _ hr)) (start + 1)
    refine ⟨.item (.object false head) tail, .cons hh ht, ?_⟩
    simp only [erase, required_propagates, he, te, List.zipIdx_cons, List.map_cons, collect]
    exact array_pair _ _

theorem leaf_consistent (ctx : Context s) (owned : OwnedContext p ctx)
    (decl : LeafField ctx.type name) (path : Path) :
    ∃ tree, AuthField s p ctx name [] .nil path tree ∧
      erase tree = interpretField (fieldShape ctx.type name) (tenantMeanings s p ctx name [])
        path (fun child atPath => (evalFields (tenantMeanings s p) .nil child atPath).map Value.object) := by
  cases ctx with
  | query => cases decl
  | project r => cases decl with
    | projectId => exact ⟨.scalar r.value.id, .projectId r owned, rfl⟩
    | projectTitle => exact ⟨.scalar r.value.title, .projectTitle r owned, rfl⟩
  | task r => cases decl with
    | taskId => exact ⟨.scalar r.value.id, .taskId r owned, rfl⟩
    | taskTitle => exact ⟨.scalar r.value.title, .taskTitle r owned, rfl⟩

theorem object_consistent (ctx : Context s) (owned : OwnedContext p ctx)
    (decl : ObjectField ctx.type name args childType) (selection : PSelection)
    (nested : ∀ child : Context s, child.type = childType → OwnedContext p child →
      ∀ path, ∃ tree, AuthTree s p child selection path tree ∧
        erase tree = (evalFields (tenantMeanings s p) selection child path).map Value.object)
    (path : Path) :
    ∃ tree, AuthField s p ctx name args selection path tree ∧
      erase tree = interpretField (fieldShape ctx.type name) (tenantMeanings s p ctx name args)
        path (fun child atPath => (evalFields (tenantMeanings s p) selection child atPath).map Value.object) := by
  cases ctx with
  | query =>
    cases decl with
    | project key =>
      cases found : projectOccurrence s p key with
      | none =>
        refine ⟨.null, .rootAbsent found, ?_⟩
        simp [tenantMeanings, found, fieldShape, Context.type, interpretField, erase]
      | some r =>
        obtain ⟨tree, ht, he⟩ := nested (.project r) rfl (lookupOccurrence_owned found).1 path
        refine ⟨.object true tree, .rootProject found ht, ?_⟩
        simp [tenantMeanings, found, fieldShape, Context.type, interpretField, erase, he]
    | projects =>
      obtain ⟨tree, ht, he⟩ := authorize_items
        ((projectOccurrences s p).map Context.project) selection
        (fun child atPath => (evalFields (tenantMeanings s p) selection child atPath).map Value.object)
        (by
          intro ctx member
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp member
          exact nested (.project r) rfl (ownedOccurrences_owned hr)) path 0
      refine ⟨.list false tree, .rootProjects ht, ?_⟩
      simp [tenantMeanings, fieldShape, Context.type, interpretField, erase, he,
        completeList, required_propagates, Function.comp_def]
  | project r =>
    cases decl with
    | tasks =>
      obtain ⟨tree, ht, he⟩ := authorize_items
        ((taskOccurrences s p r).map Context.task) selection
        (fun child atPath => (evalFields (tenantMeanings s p) selection child atPath).map Value.object)
        (by
          intro ctx member
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp member
          exact nested (.task r) rfl (taskOccurrences_owned hr)) path 0
      refine ⟨.list false tree, .tasks r owned ht, ?_⟩
      simp [tenantMeanings, fieldShape, Context.type, interpretField, erase, he,
        completeList, required_propagates, Function.comp_def]
  | task r =>
    cases decl with
    | taskProject =>
      cases found : projectOccurrence s p r.value.projectId with
      | none =>
        refine ⟨.failure false (.application .unavailable) path, .unavailable r owned found, ?_⟩
        simp [tenantMeanings, found, fieldShape, Context.type, interpretField, erase, Shape.nullable]
      | some target =>
        obtain ⟨tree, ht, he⟩ := nested (.project target) rfl (lookupOccurrence_owned found).1 path
        refine ⟨.object false tree, .taskProject r owned found ht, ?_⟩
        simp [tenantMeanings, found, fieldShape, Context.type, interpretField, erase, he]

theorem eval_fields_authorized (selection : PSelection) (ctx : Context s)
    (valid : ValidPSelection ctx.type selection) (owned : OwnedContext p ctx) (path : Path) :
    ∃ tree, AuthTree s p ctx selection path tree ∧
      erase tree = (evalFields (tenantMeanings s p) selection ctx path).map Value.object := by
  induction selection generalizing ctx path with
  | nil => exact ⟨.empty, .empty owned, rfl⟩
  | field name args children rest childrenIH restIH =>
    cases valid with
    | leaf decl unique tail =>
      obtain ⟨head, hh, he⟩ := leaf_consistent ctx owned decl (path ++ [.field name])
      obtain ⟨remaining, ht, te⟩ := restIH ctx tail owned path
      refine ⟨.field name head remaining, .field hh ht, ?_⟩
      simp only [erase, he, te, evalFields]
      exact object_pair _ _ _
    | object decl nonempty unique nested tail =>
      obtain ⟨head, hh, he⟩ := object_consistent ctx owned decl children
        (fun child same owned path => childrenIH child (same ▸ nested) owned path)
        (path ++ [.field name])
      obtain ⟨remaining, ht, te⟩ := restIH ctx tail owned path
      refine ⟨.field name head remaining, .field hh ht, ?_⟩
      simp only [erase, he, te, evalFields]
      exact object_pair _ _ _

theorem eval_authorized (valid : ValidOperation selection) :
    AuthorizedResponse s p selection (EvalSpec (tenantMeanings s p) selection) := by
  obtain ⟨tree, ht, he⟩ := eval_fields_authorized selection (.query : Context s) valid.2 trivial []
  exact ⟨valid, tree, ht, congrArg envelope he⟩

end Example.Tenant.Spec

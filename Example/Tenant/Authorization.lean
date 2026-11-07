import Example.Tenant.Evaluation

namespace Example.Tenant.Spec

/-- Untrusted witness syntax. Only AuthTree gives this syntax meaning as evidence. -/
inductive Tree where
  | empty
  | field (name : String) (value rest : Tree)
  | scalar (value : String)
  | null
  | object (nullable : Bool) (fields : Tree)
  | itemsEnd
  | item (head tail : Tree)
  | list (nullable : Bool) (items : Tree)
  | failure (nullable : Bool) (code : PublicError ApplicationError) (path : Path)

/-- Erasure has no access to principals, snapshots, or authorization proofs. -/
def erase : Tree → Result Value
  | .empty => .ok (.object []) []
  | .field name head tail => pair (fun v rest => match rest with
      | .object fields => .object ((name, v) :: fields)
      | _ => .null) (erase head) (erase tail)
  | .scalar value => .ok (.string value) []
  | .null => .ok .null []
  | .object n tree => boundary n (erase tree)
  | .itemsEnd => .ok (.array []) []
  | .item head tail => pair (fun v rest => match rest with
      | .array items => .array (v :: items)
      | _ => .null) (erase head) (erase tail)
  | .list n tree => boundary n (erase tree)
  | .failure n code path => fail n code path

mutual
  /-- Independent authorization derivation over the original surface selection. -/
  inductive AuthTree (s : Snapshot) (p : Principal) :
      Context s → PSelection → Path → Tree → Prop
    | empty (owned : OwnedContext p ctx) : AuthTree s p ctx .nil path .empty
    | field (head : AuthField s p ctx name args children (path ++ [.field name]) value)
        (tail : AuthTree s p ctx rest path remaining) :
        AuthTree s p ctx (.field name args children rest) path (.field name value remaining)

  inductive AuthField (s : Snapshot) (p : Principal) :
      Context s → String → List (String × Literal) → PSelection → Path → Tree → Prop
    | projectId (r : Occurrence s.projects) (owned : r.value.tenant = p.tenant) :
        AuthField s p (.project r) "id" [] .nil path (.scalar r.value.id)
    | projectTitle (r : Occurrence s.projects) (owned : r.value.tenant = p.tenant) :
        AuthField s p (.project r) "title" [] .nil path (.scalar r.value.title)
    | taskId (r : Occurrence s.tasks) (owned : r.value.tenant = p.tenant) :
        AuthField s p (.task r) "id" [] .nil path (.scalar r.value.id)
    | taskTitle (r : Occurrence s.tasks) (owned : r.value.tenant = p.tenant) :
        AuthField s p (.task r) "title" [] .nil path (.scalar r.value.title)
    | rootAbsent (missing : projectOccurrence s p key = none) :
        AuthField s p .query "project" [("id", .string key)] children path .null
    | rootProject (found : projectOccurrence s p key = some r)
        (nested : AuthTree s p (.project r) children path tree) :
        AuthField s p .query "project" [("id", .string key)] children path (.object true tree)
    | rootProjects
        (nested : AuthItems s p ((projectOccurrences s p).map Context.project) children path 0 tree) :
        AuthField s p .query "projects" [] children path (.list false tree)
    | tasks (r : Occurrence s.projects) (owned : r.value.tenant = p.tenant)
        (nested : AuthItems s p ((taskOccurrences s p r).map Context.task) children path 0 tree) :
        AuthField s p (.project r) "tasks" [] children path (.list false tree)
    | taskProject (r : Occurrence s.tasks) (owned : r.value.tenant = p.tenant)
        (found : projectOccurrence s p r.value.projectId = some target)
        (nested : AuthTree s p (.project target) children path tree) :
        AuthField s p (.task r) "project" [] children path (.object false tree)
    | unavailable (r : Occurrence s.tasks) (owned : r.value.tenant = p.tenant)
        (missing : projectOccurrence s p r.value.projectId = none) :
        AuthField s p (.task r) "project" [] children path
          (.failure false (.application .unavailable) path)
    | framework (owned : OwnedContext p ctx) (declared : fieldShape ctx.type name = some shape)
        (code : FrameworkError) :
        AuthField s p ctx name args children path (.failure shape.nullable (.framework code) path)

  inductive AuthItems (s : Snapshot) (p : Principal) :
      List (Context s) → PSelection → Path → Nat → Tree → Prop
    | nil : AuthItems s p [] children path index .itemsEnd
    | cons (head : AuthTree s p ctx children (path ++ [.index index]) tree)
        (tail : AuthItems s p rest children path (index + 1) remaining) :
        AuthItems s p (ctx :: rest) children path index
          (.item (.object false tree) remaining)
end

def AuthorizedResponse (s : Snapshot) (p : Principal) (selection : PSelection)
    (response : Response) : Prop :=
  ValidOperation selection ∧ ∃ tree,
    AuthTree s p .query selection [] tree ∧ envelope (erase tree) = response

theorem authTree_owned (h : AuthTree s p ctx selection path tree) : OwnedContext p ctx := by
  induction tree generalizing ctx selection path with
  | empty => cases h; assumption
  | field name value rest _ ih => cases h; apply ih; assumption
  | _ => cases h

theorem authorized_has_valid_selection (h : AuthorizedResponse s p selection response) :
    ValidOperation selection := h.1

theorem authField_owned (h : AuthField s p ctx name args children path tree) :
    OwnedContext p ctx := by
  cases h <;> simp_all [OwnedContext]

theorem authField_scalar (h : AuthField s p ctx name args children path (.scalar value)) :
    tenantMeanings s p ctx name args = .scalar value := by
  cases h <;> rfl

theorem root_list_members
    (h : AuthField s p .query name args children path (.list false tree)) :
    AuthItems s p ((projectOccurrences s p).map Context.project) children path 0 tree := by
  cases h with
  | rootProjects nested => exact nested

theorem root_object_selected
    (h : AuthField s p ctx name args children path (.object true tree))
    (root : ctx = .query) (arguments : args = [("id", .string key)]) :
    ∃ r, projectOccurrence s p key = some r ∧ AuthTree s p (.project r) children path tree := by
  cases h with
  | rootProject found nested => cases arguments; exact ⟨_, found, nested⟩

end Example.Tenant.Spec

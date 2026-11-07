import Example.Tenant.Contracts
import GraphQL.Plan.Judgment

namespace Example.Tenant.ResponseContract
open GraphQL.Plan Spec

inductive Goal (s : Snapshot) where
  | fields (ctx : Context s) (selection : PSelection) (path : Path)
  | field (ctx : Context s) (name : String) (args : List (String × Literal)) (children : PSelection) (path : Path)
  | items (rows : List (Context s)) (children : PSelection) (path : Path) (index : Nat)

/-- Local obligations on observed rows and outputs. Recursive evidence is supplied
by the generic judgment, never by an AuthTree premise. -/
inductive Rule (s : Snapshot) (p : Principal) : Goal s → List (Goal s × Tree) → Tree → Prop where
  | empty (owned : OwnedContext p ctx) : Rule s p (.fields ctx .nil path) [] .empty
  | field : Rule s p (.fields ctx (.field name args children rest) path)
      [(.field ctx name args children (path ++ [.field name]), value), (.fields ctx rest path, remaining)]
      (.field name value remaining)
  | projectId (r : Occurrence s.projects) (owned : r.value.tenant = p.tenant) :
      Rule s p (.field (.project r) "id" [] .nil path) [] (.scalar r.value.id)
  | projectTitle (r : Occurrence s.projects) (owned : r.value.tenant = p.tenant) :
      Rule s p (.field (.project r) "title" [] .nil path) [] (.scalar r.value.title)
  | taskId (r : Occurrence s.tasks) (owned : r.value.tenant = p.tenant) :
      Rule s p (.field (.task r) "id" [] .nil path) [] (.scalar r.value.id)
  | taskTitle (r : Occurrence s.tasks) (owned : r.value.tenant = p.tenant) :
      Rule s p (.field (.task r) "title" [] .nil path) [] (.scalar r.value.title)
  | rootAbsent (missing : projectOccurrence s p key = none) :
      Rule s p (.field .query "project" [("id", .string key)] children path) [] .null
  | rootProject (found : projectOccurrence s p key = some r) :
      Rule s p (.field .query "project" [("id", .string key)] children path)
        [(.fields (.project r) children path, tree)] (.object true tree)
  | rootProjects : Rule s p (.field .query "projects" [] children path)
      [(.items ((projectOccurrences s p).map Context.project) children path 0, tree)] (.list false tree)
  | tasks (r : Occurrence s.projects) (owned : r.value.tenant = p.tenant) :
      Rule s p (.field (.project r) "tasks" [] children path)
        [(.items ((taskOccurrences s p r).map Context.task) children path 0, tree)] (.list false tree)
  | taskProject (r : Occurrence s.tasks) (owned : r.value.tenant = p.tenant)
      (found : projectOccurrence s p r.value.projectId = some target) :
      Rule s p (.field (.task r) "project" [] children path)
        [(.fields (.project target) children path, tree)] (.object false tree)
  | unavailable (r : Occurrence s.tasks) (owned : r.value.tenant = p.tenant)
      (missing : projectOccurrence s p r.value.projectId = none) :
      Rule s p (.field (.task r) "project" [] children path) []
        (.failure false (.application .unavailable) path)
  | framework (owned : OwnedContext p ctx) (declared : fieldShape ctx.type name = some shape)
      (code : Example.Tenant.FrameworkError) :
      Rule s p (.field ctx name args children path) [] (.failure shape.nullable (.framework code) path)
  | itemsEnd : Rule s p (.items [] children path index) [] .itemsEnd
  | item : Rule s p (.items (ctx :: rest) children path index)
      [(.fields ctx children (path ++ [.index index]), tree), (.items rest children path (index + 1), remaining)]
      (.item (.object false tree) remaining)

def Independent (s : Snapshot) (p : Principal) : Goal s → Tree → Prop
  | .fields ctx selection path, tree => AuthTree s p ctx selection path tree
  | .field ctx name args children path, tree => AuthField s p ctx name args children path tree
  | .items rows children path index, tree => AuthItems s p rows children path index tree

theorem rules_preserve (target : Goal s) (premises : List (Goal s × Tree)) (result : Tree)
    (children : ∀ pair ∈ premises, Independent s p pair.1 pair.2)
    (law : Rule s p target premises result) : Independent s p target result := by
  cases law with
  | empty owned => exact .empty owned
  | field => exact .field (children _ List.mem_cons_self) (children _ (List.mem_cons_of_mem _ List.mem_cons_self))
  | projectId r owned => exact .projectId r owned
  | projectTitle r owned => exact .projectTitle r owned
  | taskId r owned => exact .taskId r owned
  | taskTitle r owned => exact .taskTitle r owned
  | rootAbsent missing => exact .rootAbsent missing
  | rootProject found => exact .rootProject found (children _ List.mem_cons_self)
  | rootProjects => exact .rootProjects (children _ List.mem_cons_self)
  | tasks r owned => exact .tasks r owned (children _ List.mem_cons_self)
  | taskProject r owned found => exact .taskProject r owned found (children _ List.mem_cons_self)
  | unavailable r owned missing => exact .unavailable r owned missing
  | framework owned declared code => exact .framework owned declared code
  | itemsEnd => exact .nil
  | item => exact .cons (children _ List.mem_cons_self) (children _ (List.mem_cons_of_mem _ List.mem_cons_self))

def Satisfies (s : Snapshot) (p : Principal) (selection : PSelection) (response : Response) : Prop :=
  ValidOperation selection ∧ ResponseJudgment (Rule s p) (.fields .query selection [])
    (fun tree => envelope (erase tree)) response

theorem response_authorized (proof : Satisfies s p selection response) :
    AuthorizedResponse s p selection response := by
  obtain ⟨valid, tree, derivation, erased⟩ := proof
  exact ⟨valid, tree, judgment_sound (Rule s p) (Independent s p) rules_preserve derivation, erased⟩

/-- S4 must construct these local derivations from node/row evidence while rendering.
The obligation does not assume authorization of the final response. -/
def OutputBridge (render : operation → Response) (selection : operation → PSelection)
    (s : Snapshot) (p : Principal) : Prop := ∀ op, Satisfies s p (selection op) (render op)

theorem bridge_authorized (render : operation → Response) (selection : operation → PSelection)
    (bridge : OutputBridge render selection s p) (op : operation) :
    AuthorizedResponse s p (selection op) (render op) := response_authorized (bridge op)

theorem independent_derivation (proof : AuthTree s p ctx selection path tree) :
    Judgment (Rule s p) (.fields ctx selection path) tree := by
  induction proof using AuthTree.rec
    (motive_2 := fun ctx name args children path tree _ => Judgment (Rule s p) (.field ctx name args children path) tree)
    (motive_3 := fun rows children path index tree _ => Judgment (Rule s p) (.items rows children path index) tree) with
  | empty owned => exact judgment_leaf (.empty owned)
  | field head tail headIH tailIH => exact judgment_binary headIH tailIH .field
  | projectId r owned => exact judgment_leaf (.projectId r owned)
  | projectTitle r owned => exact judgment_leaf (.projectTitle r owned)
  | taskId r owned => exact judgment_leaf (.taskId r owned)
  | taskTitle r owned => exact judgment_leaf (.taskTitle r owned)
  | rootAbsent missing => exact judgment_leaf (.rootAbsent missing)
  | rootProject found nested ih => exact judgment_unary ih (.rootProject found)
  | rootProjects nested ih => exact judgment_unary ih .rootProjects
  | tasks r owned nested ih => exact judgment_unary ih (.tasks r owned)
  | taskProject r owned found nested ih => exact judgment_unary ih (.taskProject r owned found)
  | unavailable r owned missing => exact judgment_leaf (.unavailable r owned missing)
  | framework owned declared code => exact judgment_leaf (.framework owned declared code)
  | nil => exact judgment_leaf .itemsEnd
  | cons head tail headIH tailIH => exact judgment_binary headIH tailIH .item

end Example.Tenant.ResponseContract

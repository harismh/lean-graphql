import Example.Tenant.Checks
import Example.Tenant.Conformance

namespace Example.Tenant.S0Proofs
open Spec Checks

def taskOccurrence : Occurrence snapshot.tasks := ⟨⟨1, by decide⟩⟩
def taskProjectSelection : PSelection := .field "project" [] titleSelection .nil
def tasksSelection : PSelection := .field "tasks" [] taskProjectSelection .nil
def nullableQuery : PSelection :=
  .field "project" [("id", .string "shared")] tasksSelection .nil
def requiredQuery : PSelection := .field "projects" [] tasksSelection .nil

theorem title_valid : ValidPSelection .project titleSelection :=
  .leaf .projectTitle (by simp [PSelection.names]) .nil
theorem taskProject_valid : ValidPSelection .task taskProjectSelection :=
  .object .taskProject (by decide) (by simp [PSelection.names]) title_valid .nil
theorem tasks_valid : ValidPSelection .project tasksSelection :=
  .object .tasks (by decide) (by simp [PSelection.names]) taskProject_valid .nil
theorem nullable_valid : ValidOperation nullableQuery :=
  ⟨by decide, .object (.project "shared") (by decide) (by simp [PSelection.names]) tasks_valid .nil⟩
theorem required_valid : ValidOperation requiredQuery :=
  ⟨by decide, .object .projects (by decide) (by simp [PSelection.names]) tasks_valid .nil⟩

def failurePath (root : String) (list : Bool) : Path :=
  [.field root] ++ (if list then [.index 0] else []) ++
    [.field "tasks", .index 0, .field "project"]
def unavailableAt (path : Path) : Error := ⟨.application .unavailable, path⟩

def nullableResponse : Response :=
  ⟨.object [("project", .null)], [unavailableAt (failurePath "project" false)]⟩
def requiredResponse : Response :=
  ⟨.null, [unavailableAt (failurePath "projects" true)]⟩

theorem nullable_bubbling : EvalSpec (tenantMeanings snapshot caller) nullableQuery = nullableResponse := rfl
theorem required_bubbling : EvalSpec (tenantMeanings snapshot caller) requiredQuery = requiredResponse := rfl

def taskFailureTree (path : Path) : Tree :=
  .field "project" (.failure false (.application .unavailable) (path ++ [.field "project"])) .empty
def projectFailureTree (path : Path) : Tree :=
  .field "tasks" (.list false
    (.item (.object false (taskFailureTree (path ++ [.field "tasks", .index 0]))) .itemsEnd)) .empty

theorem task_failure_authorized (path : Path) :
    AuthTree snapshot caller (.task taskOccurrence) taskProjectSelection path (taskFailureTree path) :=
  .field (.unavailable taskOccurrence (by decide) rfl) (.empty rfl)

theorem project_failure_authorized (path : Path) :
    AuthTree snapshot caller (.project ownedOccurrence) tasksSelection path (projectFailureTree path) := by
  refine .field (.tasks ownedOccurrence (by decide) (.cons ?_ .nil)) (.empty rfl)
  change AuthTree snapshot caller (.task taskOccurrence) taskProjectSelection
    ((path ++ [.field "tasks"]) ++ [.index 0])
    (taskFailureTree (path ++ [.field "tasks", .index 0]))
  rw [List.append_assoc]
  exact task_failure_authorized _

def nullableTree : Tree :=
  .field "project" (.object true (projectFailureTree [.field "project"])) .empty
def requiredTree : Tree :=
  .field "projects" (.list false
    (.item (.object false (projectFailureTree [.field "projects", .index 0])) .itemsEnd)) .empty

theorem nullable_response_authorized : AuthorizedResponse snapshot caller nullableQuery nullableResponse := by
  refine ⟨nullable_valid, nullableTree, ?_, ?_⟩
  · exact .field (.rootProject (r := ownedOccurrence) rfl (project_failure_authorized _)) (.empty trivial)
  · rfl

theorem required_response_authorized : AuthorizedResponse snapshot caller requiredQuery requiredResponse := by
  refine ⟨required_valid, requiredTree, ?_, ?_⟩
  · exact .field (.rootProjects (.cons (project_failure_authorized _) .nil)) (.empty trivial)
  · rfl

def successResponse : Response := ⟨.object [("projects", .array [.object [("title", .string "public")]])], []⟩

theorem successful_evaluation : EvalSpec (tenantMeanings snapshot caller) query = successResponse := rfl
theorem successful_response_authorized : AuthorizedResponse snapshot caller query successResponse := by
  refine ⟨valid_query, .field "projects" (.list false (.item
    (.object false (.field "title" (.scalar "public") .empty)) .itemsEnd)) .empty, ?_, ?_⟩
  · exact .field (.rootProjects (.cons
      (.field (.projectTitle ownedOccurrence (by decide)) (.empty rfl)) .nil)) (.empty trivial)
  · rfl

theorem success_conforms : Conforms query successResponse := by
  refine ⟨valid_query, .cons rfl (.list (.cons (.object ?_) .nil)) .nil⟩
  exact .cons rfl .scalar .nil
theorem nullable_conforms : Conforms nullableQuery nullableResponse :=
  ⟨nullable_valid, .cons rfl (.null rfl) .nil⟩
theorem required_conforms : Conforms requiredQuery requiredResponse :=
  ⟨required_valid, by simp [requiredResponse]⟩

def siblingQuery : PSelection :=
  .field "project" [("id", .string "shared")] tasksSelection query
def siblingResponse : Response :=
  ⟨.object [("project", .null), ("projects", .array [.object [("title", .string "public")]])],
    [unavailableAt (failurePath "project" false)]⟩

theorem nullable_preserves_sibling :
    EvalSpec (tenantMeanings snapshot caller) siblingQuery = siblingResponse := rfl
theorem filtered_index_and_single_error :
    (EvalSpec (tenantMeanings snapshot caller) requiredQuery).errors =
      [unavailableAt [.field "projects", .index 0, .field "tasks", .index 0, .field "project"]] := rfl

/-- The same fixture snapshot contains cross-tenant edges and duplicate IDs.
No global well-formedness/isolation premise was required for either witness. -/
theorem adversarial_snapshot_is_admitted :
    AuthorizedResponse snapshot caller nullableQuery nullableResponse ∧
    AuthorizedResponse snapshot caller requiredQuery requiredResponse :=
  ⟨nullable_response_authorized, required_response_authorized⟩

theorem spurious_unavailable_rejected :
    EvalSpec (tenantMeanings snapshot caller) query ≠
      ⟨successResponse.data, [unavailableAt [.field "projects"]]⟩ := by
  intro h
  have impossible : ([] : List Error) = [unavailableAt [.field "projects"]] :=
    congrArg Response.errors h
  cases impossible

def titleTree (value : String) : Tree :=
  .field "projects" (.list false
    (.item (.object false (.field "title" (.scalar value) .empty)) .itemsEnd)) .empty

theorem title_tree_exact
    (h : AuthTree snapshot caller .query query [] (titleTree value)) : value = "public" := by
  cases h with
  | field head _ =>
    have items := root_list_members head
    cases items with
    | cons object _ =>
      cases object with
      | field scalar _ =>
        have meaning := authField_scalar scalar
        exact (DomainValue.scalar.inj meaning).symm

theorem wrong_parent_tree_rejected :
    ¬ AuthTree snapshot caller .query query [] (titleTree "private") := by
  intro h
  exact (by decide : ¬ ("private" = "public")) (title_tree_exact h)

theorem forged_tree_rejected :
    ¬ AuthTree snapshot caller .query query [] (titleTree "invented") := by
  intro h
  exact (by decide : ¬ ("invented" = "public")) (title_tree_exact h)

def duplicatedOwned : Snapshot :=
  ⟨[⟨"same", 1, "first", []⟩, ⟨"same", 1, "second", []⟩], []⟩

theorem first_owned_occurrence_selected :
    (projectOccurrence duplicatedOwned caller "same").map (fun r => r.index.val) = some 0 := rfl

theorem duplicate_owned_success :
    EvalSpec (tenantMeanings duplicatedOwned caller)
      (.field "project" [("id", .string "same")] titleSelection .nil) =
        ⟨.object [("project", .object [("title", .string "first")])], []⟩ := rfl

def duplicateSelection : PSelection :=
  .field "project" [("id", .string "same")] titleSelection .nil
def shadowedTree : Tree :=
  .field "project" (.object true (.field "title" (.scalar "second") .empty)) .empty

theorem shadowed_duplicate_tree_rejected :
    ¬ AuthTree duplicatedOwned caller .query duplicateSelection [] shadowedTree := by
  intro h
  cases h with
  | field head _ =>
    obtain ⟨r, found, nested⟩ := root_object_selected head rfl rfl
    have index : r.index.val = 0 := by
      have value := congrArg (Option.map (fun r => r.index.val)) found
      simpa [first_owned_occurrence_selected] using value.symm
    cases nested with
    | field leaf _ =>
      have meaning := authField_scalar leaf
      have position : r = ⟨⟨0, by decide⟩⟩ := by
        cases r
        congr
        exact Fin.ext index
      subst position
      simp [tenantMeanings] at meaning
      exact absurd meaning (by decide)

def consistentSnapshot : Snapshot :=
  ⟨[⟨"p", 1, "project", ["t"]⟩], [⟨"t", 1, "task", "p"⟩]⟩

theorem success_conditions_inhabited : SuccessConditions consistentSnapshot caller requiredQuery :=
  ⟨required_valid, by decide, by decide, by simp [rootKeys, requiredQuery],
    by
      intro task member _
      simp [consistentSnapshot] at member
      subst member
      exact ⟨_, rfl⟩⟩

theorem consistent_snapshot_error_free :
    (EvalSpec (tenantMeanings consistentSnapshot caller) requiredQuery).errors = [] := rfl

end Example.Tenant.S0Proofs

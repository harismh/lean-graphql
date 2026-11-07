import Example.Tenant.LoweringCorrectness
import Example.Tenant.S0Proofs

namespace Example.Tenant.WaveExample
open Planning GraphQL.Plan

abbrev TaskOutcome (s : Snapshot) := Outcome ApplicationError (Occurrence s.projects)
abbrev TaskGroup (s : Snapshot) := Outcome ApplicationError (List (Occurrence s.tasks))
abbrev TaskRow (s : Snapshot) := Occurrence s.tasks × TaskOutcome s
abbrev ProjectRow (s : Snapshot) := TaskGroup s × List (TaskRow s)

def idSelection : PSelection := .field "id" [] .nil .nil
def idResolved : IR.Resolved .project idSelection := .leaf .projectId .nil (by simp [PSelection.names])

def taskBody (s : Snapshot) :
    (outputs : List Type) × (graph : TenantGraph s [TaskRow s, Principal] outputs) × Output s graph :=
  let child := compile s idResolved
  let start : TenantGraph s [TaskRow s, Principal] _ := .nil
  let raw := start.snoc (.map (fun row : TaskRow s => row.2) .here)
  let rows := raw.snoc (.map (branchRows IR.Branch.taskProject) .here)
  let frames := rows.snoc (.each .here
    (.cons (rows.inputs.rename (.there .here)) .nil) child.graph)
  let branded := frames.snoc (.map (fun values => values.map
    (fun value => (⟨value⟩ : Frame child.graph))) .here)
  ⟨_, branded, .object IR.Branch.taskProject ⟨.there (.there (.there .here))⟩ child.graph
    ⟨.here⟩ child.output .empty⟩

def projectBody (s : Snapshot) :
    (outputs : List Type) × (graph : TenantGraph s [ProjectRow s, Principal] outputs) × Output s graph :=
  let child := taskBody s
  let start : TenantGraph s [ProjectRow s, Principal] _ := .nil
  let raw := start.snoc (.map (fun row : ProjectRow s => row.1) .here)
  let rows := raw.snoc (.map (fun row : ProjectRow s => row.2) (raw.inputs.rename .here))
  let frames := rows.snoc (.each .here
    (.cons (rows.inputs.rename (.there .here)) .nil) child.2.1)
  let branded := frames.snoc (.map (fun values => values.map
    (fun value => (⟨value⟩ : Frame child.2.1))) .here)
  ⟨_, branded, .object IR.Branch.tasks ⟨.there (.there (.there .here))⟩ child.2.1
    ⟨.here⟩ child.2.2 .empty⟩

def taskLoadBody (s : Snapshot) :
    TenantGraph s [Model s .project, Principal]
      [TaskGroup s, Unit, Model s .project, Principal] :=
  .snoc (.snoc .nil (.literal .unit ()))
    (.call (branchId IR.Branch.tasks) (.there (.there .here)) (.there .here) .here)

def groupRows : TaskGroup s → List (Occurrence s.tasks)
  | .ok rows => rows
  | .error _ => []

/-- A hand-built representability witness. This is not a rewrite algorithm or its
universal correctness proof: those remain S4b. No task body invokes Task.project. -/
def wavePlan (s : Snapshot) : Operation s .query :=
  let child := projectBody s
  let start : TenantGraph s [Model s .query, Principal] _ := .nil
  let raw := start.snoc (.call (branchId IR.Branch.projects) (.there .here) .here .here)
  let projects := raw.snoc (.map (branchRows IR.Branch.projects) .here)
  let frames := projects.snoc (.each .here
    (.cons (projects.inputs.rename (.there .here)) .nil) (taskLoadBody s))
  let groups := frames.snoc (.map (fun values => values.map (fun value => value.1)) .here)
  let lists := groups.snoc (.map (fun groups : List (TaskGroup s) =>
    groups.map (fun group => (groupRows group).map (fun row => (row, ())))) .here)
  let nested := lists.snoc (.fromLists .here)
  let gathered := nested.snoc (.gather .here)
  let loaded := gathered.snoc (.vectorLoad (branchId IR.Branch.taskProject)
    (gathered.inputs.rename (.there .here)) .here)
  let scattered := loaded.snoc (.scatter .here)
  let paired := scattered.snoc (.pair (.there (.there (.there (.there (.there .here))))) .here)
  let bundled := paired.snoc (.map (fun (groups, results) =>
    List.zipWith (fun group outcomes => (group, (groupRows group).zip outcomes))
      groups results.toLists) .here)
  let region := bundled.snoc (.each .here
    (.cons (bundled.inputs.rename (.there .here)) .nil) child.2.1)
  let branded := region.snoc (.map (fun values => values.map
    (fun value => (⟨value⟩ : Frame child.2.1))) .here)
  ⟨_, branded, .object IR.Branch.projects
    ⟨.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))⟩
    child.2.1 ⟨.here⟩ child.2.2 .empty⟩

def selection : PSelection :=
  .field "projects" [] (.field "tasks" [] (.field "project" [] idSelection .nil) .nil) .nil

def selected : IR.Checked .query selection := (IR.lower .query selection).get (by decide)

theorem wave_bubbling :
    operationDenotes (meanings Checks.snapshot) (wavePlan Checks.snapshot) () Checks.caller [] =
      operationDenotes (meanings Checks.snapshot) (compile Checks.snapshot selected.val) () Checks.caller [] := rfl

theorem wave_success :
    operationDenotes (meanings S0Proofs.consistentSnapshot) (wavePlan S0Proofs.consistentSnapshot) () Checks.caller [] =
      operationDenotes (meanings S0Proofs.consistentSnapshot)
        (compile S0Proofs.consistentSnapshot selected.val) () Checks.caller [] := rfl

def multiSnapshot : Snapshot :=
  ⟨[⟨"p1", 1, "one", ["t", "missing", "t"]⟩, ⟨"empty", 1, "empty", []⟩,
    ⟨"p2", 1, "two", ["u", "t"]⟩],
    [⟨"t", 1, "task", "p1"⟩, ⟨"u", 1, "other", "p2"⟩]⟩

theorem wave_multiple_parents :
    operationDenotes (meanings multiSnapshot) (wavePlan multiSnapshot) () Checks.caller [] =
      operationDenotes (meanings multiSnapshot) (compile multiSnapshot selected.val) () Checks.caller [] := rfl

end Example.Tenant.WaveExample

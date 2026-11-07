import Example.Tenant.Occurrences
import Example.Tenant.Response

namespace Example.Tenant.Spec

inductive Context (s : Snapshot) where
  | query
  | project (row : Occurrence s.projects)
  | task (row : Occurrence s.tasks)

def Context.type : Context s → ObjectType
  | .query => .query
  | .project _ => .project
  | .task _ => .task

def OwnedContext (p : Principal) : Context s → Prop
  | .query => True
  | .project r => r.value.tenant = p.tenant
  | .task r => r.value.tenant = p.tenant

inductive DomainValue (s : Snapshot) where
  | scalar (value : String)
  | absent
  | object (row : Context s)
  | objects (rows : List (Context s))
  | unavailable
  | invalid

abbrev DomainMeanings (s : Snapshot) :=
  Context s → String → List (String × Literal) → DomainValue s

/-- Pure domain equations. No runtime resolver or generated adapter is involved. -/
def tenantMeanings (s : Snapshot) (p : Principal) : DomainMeanings s
  | .query, "project", [("id", .string key)] =>
    match projectOccurrence s p key with
    | none => .absent
    | some row => .object (.project row)
  | .query, "projects", [] => .objects ((projectOccurrences s p).map Context.project)
  | .project row, "tasks", [] => .objects ((taskOccurrences s p row).map Context.task)
  | .task row, "project", [] =>
    match projectOccurrence s p row.value.projectId with
    | none => .unavailable
    | some target => .object (.project target)
  | .project row, "id", [] => .scalar row.value.id
  | .project row, "title", [] => .scalar row.value.title
  | .task row, "id", [] => .scalar row.value.id
  | .task row, "title", [] => .scalar row.value.title
  | _, _, _ => .invalid

def fail (nullable : Bool) (code : PublicError ApplicationError) (path : Path) :=
  boundary nullable (.bubble [⟨code, path⟩])

/-- Total field interpretation, with recursion supplied only for strict child selections. -/
def interpretField (shape : Option Shape) (value : DomainValue s) (path : Path)
    (child : Context s → Path → Result Value) : Result Value :=
  match shape, value with
  | some (.scalar n), .scalar text => boundary n (.ok (.string text) [])
  | some (.object _ true), .absent => .ok .null []
  | some (.object _ n), .object ctx => boundary n (child ctx path)
  | some (.list _ n en), .objects rows =>
    completeList n en (rows.zipIdx.map (fun (ctx, i) => child ctx (path ++ [.index i])))
  | some shape, .unavailable => fail shape.nullable (.application .unavailable) path
  | some shape, _ => fail shape.nullable (.framework .argument) path
  | none, _ => fail false (.framework .argument) path

/-- Structural recursion on surface selections, independent of runtime fuel.
Malformed selections have a total interpretation too; guarantees quantify over ValidOperation. -/
def evalFields (meanings : DomainMeanings s) :
    PSelection → Context s → Path → Result (List (String × Value))
  | .nil, _, _ => .ok [] []
  | .field name args children rest, ctx, path =>
    let fieldPath := path ++ [.field name]
    let value := interpretField (fieldShape ctx.type name) (meanings ctx name args) fieldPath
      (fun child childPath => (evalFields meanings children child childPath).map Value.object)
    pair (fun v fields => (name, v) :: fields) value (evalFields meanings rest ctx path)

def EvalSpec (meanings : DomainMeanings s) (selection : PSelection) : Response :=
  envelope ((evalFields meanings selection .query []).map Value.object)

def rootKeys : PSelection → List String
  | .nil => []
  | .field "project" [("id", .string key)] _ rest => key :: rootKeys rest
  | .field _ _ _ rest => rootKeys rest

/-- Explicit sufficient domain hypotheses for the later universal error-free theorem.
They are not premises of response authorization. -/
structure SuccessConditions (s : Snapshot) (p : Principal) (selection : PSelection) : Prop where
  valid : ValidOperation selection
  uniqueProjects : (s.projects.map Project.id).Nodup
  uniqueTasks : (s.tasks.map Task.id).Nodup
  rootLookups : ∀ key ∈ rootKeys selection,
    ∃ row, projectOccurrence s p key = some row
  requiredTargets : ∀ task ∈ s.tasks, task.tenant = p.tenant →
    ∃ row, projectOccurrence s p task.projectId = some row

end Example.Tenant.Spec

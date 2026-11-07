import Example.Tenant.PlanSchema
import Example.Tenant.CompletionBridge
import Example.Tenant.Consistency

namespace Example.Tenant.Planning
open GraphQL.Plan

abbrev TenantGraph (s : Snapshot) := Graph schema (models s) Principal ApplicationError
abbrev TenantNode (s : Snapshot) := Node schema (models s) Principal ApplicationError
abbrev Backend (s : Snapshot) := Meanings schema (models s) Principal ApplicationError

def appendField (name : String) (head tail : Spec.Result Spec.Value) : Spec.Result Spec.Value :=
  Spec.fromCompletion (Completion.pair (Spec.objectCons name)
    (Spec.toCompletion head) (Spec.toCompletion tail))

theorem appendField_eq (name : String) (head tail : Spec.Result Spec.Value) :
    appendField name head tail = Spec.pair (Spec.objectCons name) head tail := by
  rw [appendField, ← Spec.completion_pair, Spec.completion_roundtrip]

def completeRows (rows : List (Spec.Result Spec.Value)) : Spec.Result Spec.Value :=
  Spec.fromCompletion ((Completion.collect (rows.map Spec.toCompletion)).map Spec.Value.array)

theorem completeRows_eq (rows : List (Spec.Result Spec.Value)) :
    completeRows rows = Spec.completeList false false rows := by
  rw [completeRows, ← Spec.completion_collect, ← Spec.completion_map, Spec.completion_roundtrip]
  simp [Spec.completeList, show Spec.boundary false = id from funext Spec.required_propagates]

def renderLeaf {carriers : Fin 3 → Type} (field : IR.Leaf object)
    (raw : Outcome ApplicationError ((leafId field).Out carriers)) (path : Spec.Path) :
    Spec.Result Spec.Value :=
  match raw with
  | .ok value => .ok (.string (leafString field value)) []
  | .error error => Spec.fail false (errorCode error) path

def renderSingle (nullable : Bool) (path : Spec.Path) : List (Spec.Result Spec.Value) → Spec.Result Spec.Value
  | [] => Spec.fail nullable (.framework .internal) path
  | first :: _ => Spec.boundary nullable first

def renderBranch {carriers : Fin 3 → Type} (field : IR.Branch parent child)
    (raw : Outcome ApplicationError ((branchId field).Out carriers))
    (completed : List (Spec.Result Spec.Value)) (path : Spec.Path) : Spec.Result Spec.Value :=
  match raw with
  | .error error => Spec.fail (isNullable field) (errorCode error) path
  | .ok value => match field with
    | .project => match value with
      | none => .ok .null []
      | some _ => renderSingle true path completed
    | .projects | .tasks => completeRows completed
    | .taskProject => renderSingle false path completed

def childPath (field : IR.Branch parent child) (path : Spec.Path) (index : Nat) : Spec.Path :=
  if isList field then path ++ [.index index] else path

/-- Output identity is indexed by the exact execution graph, independently of fetch IDs. -/
inductive OutputFor (carriers : Fin 3 → Type) (scope : Type) :
    {input output : List Type} → Graph schema carriers scope ApplicationError input output → Type 1 where
  | empty : OutputFor carriers scope graph
  | leaf (field : IR.Leaf object)
      (value : OutputRef graph (Outcome ApplicationError ((leafId field).Out carriers)))
      (tail : OutputFor carriers scope graph) : OutputFor carriers scope graph
  /-- Arbitrary body inputs allow rewrites to supply precomputed, scattered outcomes. -/
  | object (field : IR.Branch parent child)
      (value : OutputRef graph (Outcome ApplicationError ((branchId field).Out carriers)))
      (body : Graph schema carriers scope ApplicationError childInputs childOutputs)
      (frames : OutputRef graph (List (Frame body)))
      (children : OutputFor carriers scope body) (tail : OutputFor carriers scope graph) : OutputFor carriers scope graph
  | weaken {input output : List Type} {graph : Graph schema carriers scope ApplicationError input output}
      (prior : OutputFor carriers scope graph) (node : Node schema carriers scope ApplicationError output a) :
      OutputFor carriers scope (.snoc graph node)

abbrev Output (s : Snapshot) {input output : List Type} (graph : TenantGraph s input output) :=
  OutputFor (models s) Principal graph

def render {carriers : Fin 3 → Type} {scope : Type}
    {input output : List Type} {graph : Graph schema carriers scope ApplicationError input output} : OutputFor carriers scope graph → Frame graph → Spec.Path → Spec.Result Spec.Value
  | .empty, _, _ => .ok (.object []) []
  | .leaf field value tail, frame, path =>
    appendField field.name (renderLeaf field (value.read frame) (path ++ [.field field.name]))
      (render tail frame path)
  | .object field value _ frames children tail, frame, path =>
    let fieldPath := path ++ [.field field.name]
    let completed := (frames.read frame).zipIdx.map (fun (child, i) => render children child (childPath field fieldPath i))
    appendField field.name (renderBranch field (value.read frame) completed fieldPath) (render tail frame path)
  | .weaken prior _, frame, path => render prior ⟨frame.value.2⟩ path

theorem render_weaken {carriers : Fin 3 → Type} {scope : Type} {graph : Graph schema carriers scope ApplicationError input output} (out : OutputFor carriers scope graph) (node : Node schema carriers scope ApplicationError output a)
    (backend : Meanings schema carriers scope ApplicationError) (values : Values input) (path : Spec.Path) :
    render (.weaken out node) (runDenotation backend (.snoc graph node) values) path =
      render out (runDenotation backend graph values) path := rfl

def branchCall {carriers : Fin 3 → Type} {scope : Type}
    (backend : Meanings schema carriers scope ApplicationError) (field : IR.Branch parent child) (principal : scope)
    (parentValue : carriers (objectId parent)) (args : field.Args) (error : Option Example.Tenant.FrameworkError) :
    Outcome ApplicationError ((branchId field).Out carriers) :=
  match error with
  | some code => .error (.framework (frameworkCode code))
  | none => backend (branchId field) principal parentValue (branchArgs field args)

/-- Denotation of typed selections; no surface interpreter or graph interpreter is called. -/
def denoteResolved {carriers : Fin 3 → Type} {scope : Type}
    (backend : Meanings schema carriers scope ApplicationError) : IR.Resolved object selection →
    carriers (objectId object) → scope → Spec.Path → Spec.Result Spec.Value
  | .nil, _, _, _ => .ok (.object []) []
  | .leaf field rest _, parent, principal, path =>
    appendField field.name
      (renderLeaf field (backend (leafId field) principal parent (leafArgs field)) (path ++ [.field field.name]))
      (denoteResolved backend rest parent principal path)
  | .object field args error children _ rest _, parent, principal, path =>
    let fieldPath := path ++ [.field field.name]
    let raw := branchCall backend field principal parent args error
    let completed := (branchRows field raw).zipIdx.map (fun (child, i) =>
      denoteResolved backend children child principal (childPath field fieldPath i))
    appendField field.name (renderBranch field raw completed fieldPath)
      (denoteResolved backend rest parent principal path)

end Example.Tenant.Planning

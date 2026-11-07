import Example.Tenant.OutputPlan

namespace Example.Tenant.Planning
open GraphQL.Plan

structure OperationFor (carriers : Fin 3 → Type) (scope : Type) (object : ObjectType) where
  outputs : List Type
  graph : Graph schema carriers scope ApplicationError [carriers (objectId object), scope] outputs
  output : OutputFor carriers scope graph

abbrev Operation (s : Snapshot) := OperationFor (models s) Principal

def operationDenotes {carriers : Fin 3 → Type} {scope : Type}
    (backend : Meanings schema carriers scope ApplicationError) (operation : OperationFor carriers scope object)
    (parent : carriers (objectId object)) (principal : scope) (path : Spec.Path) : Spec.Result Spec.Value :=
  render operation.output (runDenotation backend operation.graph (parent, principal, ())) path

def callNode {carriers : Fin 3 → Type} {scope : Type} (field : IR.Branch parent child) (error : Option Example.Tenant.FrameworkError)
    (token : Ref inputs scope) (row : Ref inputs (carriers (objectId parent)))
    (args : Ref inputs (branchId field).Args) :
    Node schema carriers scope ApplicationError inputs (Outcome ApplicationError ((branchId field).Out carriers)) :=
  match error with
  | none => .call (branchId field) token row args
  | some code => .map (fun _ : scope => .error (.framework (frameworkCode code))) token

/-- Builds an acyclic graph and a separate output plan. It never calls EvalSpec. -/
def compileFor (carriers : Fin 3 → Type) (scope : Type) :
    IR.Resolved object selection → OperationFor carriers scope object
  | .nil => ⟨_, .nil, .empty⟩
  | .leaf field rest _ =>
    let tail := compileFor carriers scope rest
    let argsNode := Node.literal (leafId field).decl.input (leafArgs field)
    let argsGraph := tail.graph.snoc argsNode
    let token := tail.graph.inputs.rename (.there .here)
    let parent := tail.graph.inputs.rename .here
    let invoke := Node.call (leafId field) (.there token) (.there parent) .here
    ⟨_, argsGraph.snoc invoke,
      .leaf field ⟨.here⟩ (.weaken (.weaken tail.output argsNode) invoke)⟩
  | .object field args error children _ rest _ =>
    let tail := compileFor carriers scope rest
    let child := compileFor carriers scope children
    let token := tail.graph.inputs.rename (.there .here)
    let parent := tail.graph.inputs.rename .here
    let argsNode := Node.literal (branchId field).decl.input (branchArgs field args)
    let argsGraph := tail.graph.snoc argsNode
    let invoke := callNode field error (.there token) (.there parent) .here
    let callGraph := argsGraph.snoc invoke
    let rowsNode := Node.map (branchRows field) .here
    let rowsGraph := callGraph.snoc rowsNode
    let region := Node.each .here (.cons (.there (.there (.there token))) .nil) child.graph
    let regionGraph := rowsGraph.snoc region
    let brand := Node.map (fun frames => frames.map (fun values => (⟨values⟩ : Frame child.graph))) .here
    let finalGraph := regionGraph.snoc brand
    ⟨_, finalGraph, .object field ⟨.there (.there (.there .here))⟩ child.graph ⟨.here⟩ child.output
      (.weaken (.weaken (.weaken (.weaken (.weaken tail.output argsNode) invoke) rowsNode) region) brand)⟩

abbrev compile (s : Snapshot) {object : ObjectType} {selection : PSelection}
    (resolved : IR.Resolved object selection) := compileFor (models s) Principal resolved

theorem compile_for_correct {carriers : Fin 3 → Type} {scope : Type}
    (resolved : IR.Resolved object selection) (backend : Meanings schema carriers scope ApplicationError)
    (parent : carriers (objectId object)) (principal : scope) (path : Spec.Path) :
    operationDenotes backend (compileFor carriers scope resolved) parent principal path =
      denoteResolved backend resolved parent principal path := by
  induction resolved generalizing principal path with
  | nil => rfl
  | leaf field rest fresh ih =>
    simp only [compileFor, operationDenotes, render, runDenotation, denoteGraph, denoteNode,
      OutputRef.read, Ref.read]
    simp only [graph_input_read, Ref.read]
    exact congrArg _ (ih parent principal path)
  | object field args error children nonempty rest fresh childIH restIH =>
    simp only [compileFor, operationDenotes, render, runDenotation, denoteGraph, denoteNode,
      OutputRef.read, Ref.read, Capture.read, graph_input_read]
    have childrenCorrect := childIH
    have restCorrect := restIH
    simp only [operationDenotes, runDenotation] at childrenCorrect restCorrect
    cases error <;>
      simp [callNode, denoteNode, Ref.read, graph_input_read, denoteResolved, branchCall,
        childrenCorrect, restCorrect, List.map_map, Function.comp_def, List.zipIdx_map]

theorem compile_correct (resolved : IR.Resolved object selection) (backend : Backend s)
    (parent : Model s object) (principal : Principal) (path : Spec.Path) :
    operationDenotes backend (compile s resolved) parent principal path =
      denoteResolved backend resolved parent principal path :=
  compile_for_correct resolved backend parent principal path

end Example.Tenant.Planning

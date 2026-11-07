import GraphQL.Plan.Schema
import GraphQL.Plan.CallDenotation
import GraphQL.Plan.Rows

namespace GraphQL.Plan

abbrev Values : List Type → Type
  | [] => Unit
  | a :: rest => a × Values rest

inductive Ref : List Type → Type → Type 1 where
  | here : Ref (a :: rest) a
  | there (ref : Ref rest a) : Ref (b :: rest) a

def Ref.read : Ref context a → Values context → a
  | .here, values => values.1
  | .there ref, values => ref.read values.2

inductive Capture (source : List Type) : List Type → Type 1 where
  | nil : Capture source []
  | cons (head : Ref source a) (tail : Capture source rest) : Capture source (a :: rest)

def Capture.read : Capture source target → Values source → Values target
  | .nil, _ => ()
  | .cons head tail, values => (head.read values, tail.read values)

/-- Structural context embeddings preserve the order of old dependencies. -/
inductive Embedding : List Type → List Type → Type 1 where
  | nil : Embedding [] []
  | keep (rest : Embedding source target) : Embedding (a :: source) (a :: target)
  | skip (rest : Embedding source target) : Embedding source (a :: target)

def Embedding.rename : Embedding source target → Ref source a → Ref target a
  | .nil, ref => nomatch ref
  | .keep rest, .here => .here
  | .keep rest, .there ref => .there (rest.rename ref)
  | .skip rest, ref => .there (rest.rename ref)

def Embedding.project : Embedding source target → Values target → Values source
  | .nil, _ => ()
  | .keep rest, values => (values.1, rest.project values.2)
  | .skip rest, values => rest.project values.2

def Embedding.identity : (context : List Type) → Embedding context context
  | [] => .nil
  | _ :: rest => .keep (identity rest)

theorem identity_project (values : Values context) :
    (Embedding.identity context).project values = values := by
  induction context with
  | nil => cases values; rfl
  | cons head tail ih => exact congrArg (Prod.mk values.1) (ih values.2)

theorem renamed_read (embedding : Embedding source target) (ref : Ref source a)
    (values : Values target) :
    (embedding.rename ref).read values = ref.read (embedding.project values) := by
  induction embedding with
  | nil => cases ref
  | keep rest ih => cases ref <;> simp [Embedding.rename, Embedding.project, Ref.read, ih]
  | skip rest ih => exact ih ref values.2

/-- The tag is erased at runtime but prevents substituting a different graph's frame. -/
structure Tagged {α : Sort u} (tag : α) (valueType : Type) where
  value : valueType

mutual
  /-- A node can read only the already-built prior; no forward or cyclic references. -/
  inductive Graph (schema : Schema) (models : Fin schema.objectCount → Type)
      (scope app : Type) : List Type → List Type → Type 1 where
    | nil : Graph schema models scope app input input
    | snoc (prior : Graph schema models scope app input context)
        (node : Node schema models scope app context result) :
        Graph schema models scope app input (result :: context)

  inductive Node (schema : Schema) (models : Fin schema.objectCount → Type)
      (scope app : Type) : List Type → Type → Type 1 where
    | literal (type : InputType) (value : type.denote) : Node schema models scope app context type.denote
    | map (function : a → b) (input : Ref context a) : Node schema models scope app context b
    | pair (left : Ref context a) (right : Ref context b) : Node schema models scope app context (a × b)
    | call {object : Fin schema.objectCount} (field : FieldId schema object)
        (token : Ref context scope) (parent : Ref context (models object)) (args : Ref context field.Args) :
        Node schema models scope app context (Outcome app (field.Out models))
    | gather (rows : Ref context (Nested a)) : Node schema models scope app context (Gathered a)
    | scatter (rows : Ref context (Gathered a)) : Node schema models scope app context (Nested a)
    | fromLists (rows : Ref context (List (List a))) : Node schema models scope app context (Nested a)
    | vectorLoad {object : Fin schema.objectCount} (field : FieldId schema object)
        (token : Ref context scope) (rows : Ref context (Gathered (models object × field.Args))) :
        Node schema models scope app context (Gathered (Outcome app (field.Out models)))
    | each (input : Ref context (List a)) (captures : Capture context captured)
        (body : Graph schema models scope app (a :: captured) outputs) :
        Node schema models scope app context (List (Values outputs))
    | mapRows (input : Ref context (Gathered a)) (captures : Capture context captured)
        (body : Graph schema models scope app (a :: captured) outputs) (result : Ref outputs b) :
        Node schema models scope app context (Gathered b)
end

abbrev Frame (graph : Graph schema models scope app input output) := Tagged graph (Values output)

mutual
  def denoteGraph (meanings : Meanings schema models scope app) :
      Graph schema models scope app input output → Values input → Values output
    | .nil, values => values
    | .snoc prior node, values =>
      let previous := denoteGraph meanings prior values
      (denoteNode meanings node previous, previous)

  def denoteNode (meanings : Meanings schema models scope app) :
      Node schema models scope app context result → Values context → result
    | .literal _ value, _ => value
    | .map f input, values => f (input.read values)
    | .pair left right, values => (left.read values, right.read values)
    | .call field token parent args, values => meanings field (token.read values) (parent.read values) (args.read values)
    | .gather rows, values => gather (rows.read values)
    | .scatter rows, values => scatter (rows.read values)
    | .fromLists rows, values => Nested.ofLists (rows.read values)
    | .vectorLoad field token rows, values =>
      (rows.read values).map (fun (parent, args) => meanings field (token.read values) parent args)
    | .each input captures body, values =>
      (input.read values).map (fun row => denoteGraph meanings body (row, captures.read values))
    | .mapRows input captures body result, values =>
      (input.read values).map (fun row => result.read (denoteGraph meanings body (row, captures.read values)))
end

structure OutputRef (graph : Graph schema models scope app input output) (a : Type) where
  ref : Ref output a

def OutputRef.read (ref : OutputRef graph a) (frame : Frame graph) : a := ref.ref.read frame.value

def runDenotation (meanings : Meanings schema models scope app)
    (graph : Graph schema models scope app input output) (values : Values input) : Frame graph :=
  ⟨denoteGraph meanings graph values⟩

def Graph.inputs : Graph schema models scope app input output → Embedding input output
  | .nil => Embedding.identity _
  | .snoc prior _ => .skip prior.inputs

theorem graph_inputs_project (graph : Graph schema models scope app input output)
    (meanings : Meanings schema models scope app) (values : Values input) :
    graph.inputs.project (denoteGraph meanings graph values) = values := by
  cases graph with
  | nil => exact identity_project values
  | snoc prior node => exact graph_inputs_project prior meanings values

theorem graph_input_read (graph : Graph schema models scope app input output)
    (meanings : Meanings schema models scope app) (values : Values input) (ref : Ref input a) :
    (graph.inputs.rename ref).read (denoteGraph meanings graph values) = ref.read values := by
  rw [renamed_read, graph_inputs_project]

theorem prior_preserved (meanings : Meanings schema models scope app)
    (prior : Graph schema models scope app input context)
    (node : Node schema models scope app context result) (ref : Ref context a) (values : Values input) :
    (Ref.there ref).read (denoteGraph meanings (.snoc prior node) values) =
      ref.read (denoteGraph meanings prior values) := rfl

theorem gather_scatter_denotation (meanings : Meanings schema models scope app)
    (ref : Ref context (Nested a)) (values : Values context) :
    denoteNode meanings (.scatter (Ref.here : Ref (Gathered a :: context) (Gathered a)))
      (denoteNode meanings (.gather ref) values, values) = ref.read values :=
  scatter_gather _

theorem vector_load_position (meanings : Meanings schema models scope app)
    (field : FieldId schema object) (token : Ref context scope)
    (rows : Ref context (Gathered (models object × field.Args))) (values : Values context)
    (i : Fin (rows.read values).count) (j : Fin ((rows.read values).width i)) :
    ((scatter (denoteNode meanings (.vectorLoad field token rows) values)).values i).get j =
      meanings field (token.read values) ((rows.read values).getValue ⟨i, j⟩).1
        ((rows.read values).getValue ⟨i, j⟩).2 := by
  exact scatter_map_at _ _ i j

theorem node_call_bridge (meanings : Meanings schema models scope app)
    (field : FieldId schema object) (token : Ref context scope)
    (parent : Ref context (models object)) (args : Ref context field.Args) (values : Values context) :
    denoteNode meanings (.call field token parent args) values =
      denoteCall meanings (.one field (token.read values) (parent.read values) (args.read values)) := rfl

theorem vector_call_bridge (meanings : Meanings schema models scope app)
    (field : FieldId schema object) (token : Ref context scope)
    (rows : Ref context (Gathered (models object × field.Args))) (values : Values context) :
    (denoteNode meanings (.vectorLoad field token rows) values).materialize =
      denoteCall meanings (.batch field (token.read values) (rows.read values).materialize) :=
  materialize_map _ _

theorem map_rows_position (meanings : Meanings schema models scope app)
    (rows : Ref context (Gathered a)) (captures : Capture context captured)
    (body : Graph schema models scope app (a :: captured) outputs) (result : Ref outputs b)
    (values : Values context) (i : Fin (rows.read values).count)
    (j : Fin ((rows.read values).width i)) :
    ((scatter (denoteNode meanings (.mapRows rows captures body result) values)).values i).get j =
      result.read (denoteGraph meanings body ((rows.read values).getValue ⟨i, j⟩, captures.read values)) :=
  scatter_map_at _ _ i j

end GraphQL.Plan

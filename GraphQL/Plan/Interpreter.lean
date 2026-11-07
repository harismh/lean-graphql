import GraphQL.Plan.Machine

namespace GraphQL.Plan

abbrev Execution (schema : Schema) (models : Fin schema.objectCount → Type) (scope app : Type) :=
  Machine (Call schema models scope) (Answer app)

variable {schema : Schema} {models : Fin schema.objectCount → Type} {scope app : Type}

def traverseRows (rows : Gathered α) (f : RowIndex rows.width → Machine C A β) : Machine C A (Gathered β) :=
  (tabulate (fun i => tabulate (fun j => f ⟨i, j⟩))).bind
    (fun values => .done ⟨rows.count, rows.width, fun index => values index.1 index.2⟩)

theorem run_traverse_rows {C : Type} {A : C → Type} (resolve : (call : C) → A call)
    (rows : Gathered α) (f : RowIndex rows.width → Machine C A β) :
    runMachine resolve (traverseRows rows f) =
      ⟨rows.count, rows.width, fun index => runMachine resolve (f index)⟩ := by
  simp only [traverseRows, run_bind, runMachine, run_tabulate]

theorem sat_traverse_rows (rows : Gathered α) (f : RowIndex rows.width → Machine C A β)
    (relation : RowIndex rows.width → β → Prop) (valid : ∀ index, Sat pre post (f index) (relation index))
    (Q : Gathered β → Prop) (close : ∀ answers, (∀ index, relation index (answers index)) →
      Q ⟨rows.count, rows.width, answers⟩) : Sat pre post (traverseRows rows f) Q := by
  apply sat_bind _ _ (sat_tabulate _ _ (fun i => sat_tabulate _ _ (fun j => valid ⟨i, j⟩)))
  intro answers holds
  exact close _ (fun index => holds index.1 index.2)

mutual
  def interpretGraph : Graph schema models scope app input output → Values input → Execution schema models scope app (Values output)
    | .nil, values => .done values
    | .snoc prior node, values => (interpretGraph prior values).bind (fun previous =>
      (interpretNode node previous).bind (fun result => .done (result, previous)))

  def interpretNode : Node schema models scope app context result → Values context → Execution schema models scope app result
    | .literal _ value, _ => .done value
    | .map f input, values => .done (f (input.read values))
    | .pair left right, values => .done (left.read values, right.read values)
    | .call field token parent args, values =>
      .pending (.one field (token.read values) (parent.read values) (args.read values)) .done
    | .gather rows, values => .done (gather (rows.read values))
    | .scatter rows, values => .done (scatter (rows.read values))
    | .fromLists rows, values => .done (Nested.ofLists (rows.read values))
    | .vectorLoad field token rows, values => traverseRows (rows.read values) (fun index =>
      .pending (.one field (token.read values) ((rows.read values).getValue index).1
        ((rows.read values).getValue index).2) .done)
    | .each input captures body, values => traverse (fun row => interpretGraph body (row, captures.read values)) (input.read values)
    | .mapRows input captures body result, values => traverseRows (input.read values) (fun index =>
      (interpretGraph body ((input.read values).getValue index, captures.read values)).bind
        (fun output => .done (result.read output)))
end

theorem interpreter_denotation (graph : Graph schema models scope app input output)
    (backend : Meanings schema models scope app) (values : Values input) :
    runMachine (denoteCall backend) (interpretGraph graph values) = denoteGraph backend graph values := by
  induction graph using Graph.rec
    (motive_2 := fun _ _ node => ∀ values, runMachine (denoteCall backend) (interpretNode node values) = denoteNode backend node values) with
  | nil => rfl
  | snoc prior node priorIH nodeIH => simp only [interpretGraph, run_bind, runMachine, priorIH, nodeIH, denoteGraph]
  | literal | map | pair | call | gather | scatter | fromLists => rfl
  | vectorLoad => simp only [interpretNode, run_traverse_rows, runMachine, denoteCall, denoteNode, Gathered.map]
  | each input captures body ih => simp only [interpretNode, run_traverse, ih, denoteNode]
  | mapRows input captures body result ih => simp only [interpretNode, run_traverse_rows, run_bind, runMachine, ih, denoteNode, Gathered.map]

theorem graph_contract_execution {input output : List Type}
    {graph : Graph schema models scope app input output} {contracts : Contracts schema models scope app}
    {P : Values input → Prop} {Q : Values output → Prop} (proof : GraphProof contracts graph P Q)
    (values : Values input) (valid : P values) :
    Sat contracts.Pre contracts.Post (interpretGraph graph values) Q := by
  revert values
  induction proof using GraphProof.rec
    (motive_2 := fun node P Q _ => ∀ values, P values →
      Sat contracts.Pre contracts.Post (interpretNode node values) (Q values)) with
  | nil close => exact close
  | snoc prior step close priorIH stepIH =>
    intro values valid
    apply sat_bind _ _ (priorIH values valid)
    intro previous holds
    apply sat_bind _ _ (stepIH previous holds)
    exact fun result good => close previous holds result good
  | literal close | map close | pair close | gather close | scatter close | fromLists close => exact close _ ‹_›
  | call ready close =>
    rename_i values valid
    exact ⟨ready values valid, fun answer post => close values valid answer post⟩
  | vectorLoad ready close =>
    rename_i field token rows P Q values valid
    simp only [interpretNode]
    refine sat_traverse_rows _ _ (fun index answer => contracts.post field (token.read values)
      ((rows.read values).getValue index).1 ((rows.read values).getValue index).2 answer) ?_ _ ?_
    · intro index
      exact ⟨ready values valid index, fun answer post => post⟩
    · exact close values valid
  | each bodyProof close ih =>
    rename_i values valid
    exact sat_weaken _ (sat_traverse _ _ (fun row member => ih values valid row member _ rfl)) (close values valid)
  | mapRows bodyProof close ih =>
    rename_i input captures body result P Q relation values valid
    simp only [interpretNode]
    refine sat_traverse_rows _ _ (relation values) ?_ _ ?_
    · intro index
      apply sat_bind _ _ (ih values valid index _ rfl)
      exact fun output good => good
    · exact close values valid

end GraphQL.Plan

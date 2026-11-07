import GraphQL.Plan.Graph

namespace GraphQL.Plan

variable {schema : Schema} {models : Fin schema.objectCount → Type} {scope app : Type}

def BackendSatisfies (contracts : Contracts schema models scope app)
    (backend : Meanings schema models scope app) : Prop :=
  ∀ {object} (field : FieldId schema object) token parent args,
    contracts.pre field token parent args → contracts.post field token parent args (backend field token parent args)

inductive RelatedLists (relation : α → β → Prop) : List α → List β → Prop where
  | nil : RelatedLists relation [] []
  | cons : relation a b → RelatedLists relation as bs → RelatedLists relation (a :: as) (b :: bs)

theorem forall2_mapped (rows : List α) (f : α → β) (relation : α → β → Prop)
    (holds : ∀ row ∈ rows, relation row (f row)) : RelatedLists relation rows (rows.map f) := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (holds head List.mem_cons_self) (ih (fun row member => holds row (List.mem_cons_of_mem _ member)))

/- Syntax-directed certificates cover every graph node. Postconditions are arbitrary
predicates on complete values, so they can express list bounds and correlations,
not just elementwise ownership. Pure maps require an explicit closure proof. -/
mutual
  inductive GraphProof (contracts : Contracts schema models scope app) :
      {input output : List Type} → Graph schema models scope app input output → (Values input → Prop) → (Values output → Prop) → Prop where
    | nil {context : List Type} {P Q : Values context → Prop} (close : ∀ values, P values → Q values) : GraphProof contracts .nil P Q
    | snoc {graph : Graph schema models scope app input context} {node : Node schema models scope app context a}
        {P : Values input → Prop} {R : Values context → Prop} {S : Values context → a → Prop}
        {Q : Values (a :: context) → Prop} (prior : GraphProof contracts graph P R) (step : NodeProof contracts node R S)
        (close : ∀ values, R values → ∀ result, S values result → Q (result, values)) :
        GraphProof contracts (.snoc graph node) P Q

  inductive NodeProof (contracts : Contracts schema models scope app) :
      {context : List Type} → {result : Type} → Node schema models scope app context result → (Values context → Prop) →
        (Values context → result → Prop) → Prop where
    | literal {kind : InputType} {value : kind.denote}
        {P : Values context → Prop} {Q : Values context → kind.denote → Prop} (close : ∀ values, P values → Q values value) :
        NodeProof contracts (.literal kind value) P Q
    | map {input : Ref context a} {f : a → b}
        {P : Values context → Prop} {Q : Values context → b → Prop} (close : ∀ values, P values → Q values (f (input.read values))) :
        NodeProof contracts (.map f input) P Q
    | pair {left : Ref context a} {right : Ref context b}
        {P : Values context → Prop} {Q : Values context → (a × b) → Prop} (close : ∀ values, P values → Q values (left.read values, right.read values)) :
        NodeProof contracts (.pair left right) P Q
    | call {field : FieldId schema object} {token : Ref context scope} {parent : Ref context (models object)}
        {args : Ref context field.Args} {P : Values context → Prop}
        {Q : Values context → Outcome app (field.Out models) → Prop} (ready : ∀ values, P values → contracts.pre field (token.read values) (parent.read values) (args.read values))
        (close : ∀ values, P values → ∀ result,
          contracts.post field (token.read values) (parent.read values) (args.read values) result → Q values result) :
        NodeProof contracts (.call field token parent args) P Q
    | gather {rows : Ref context (Nested a)}
        {P : Values context → Prop} {Q : Values context → Gathered a → Prop} (close : ∀ values, P values → Q values (gather (rows.read values))) :
        NodeProof contracts (.gather rows) P Q
    | scatter {rows : Ref context (Gathered a)}
        {P : Values context → Prop} {Q : Values context → Nested a → Prop} (close : ∀ values, P values → Q values (scatter (rows.read values))) :
        NodeProof contracts (.scatter rows) P Q
    | fromLists {rows : Ref context (List (List a))}
        {P : Values context → Prop} {Q : Values context → Nested a → Prop} (close : ∀ values, P values → Q values (Nested.ofLists (rows.read values))) :
        NodeProof contracts (.fromLists rows) P Q
    | vectorLoad {field : FieldId schema object} {token : Ref context scope}
        {rows : Ref context (Gathered (models object × field.Args))}
        {P : Values context → Prop} {Q : Values context → Gathered (Outcome app (field.Out models)) → Prop}
        (ready : ∀ values, P values → ∀ index,
          contracts.pre field (token.read values) ((rows.read values).getValue index).1 ((rows.read values).getValue index).2)
        (close : ∀ values, P values → ∀ answers,
          (∀ index, contracts.post field (token.read values) ((rows.read values).getValue index).1
            ((rows.read values).getValue index).2 (answers index)) →
          Q values ⟨(rows.read values).count, (rows.read values).width, answers⟩) :
        NodeProof contracts (.vectorLoad field token rows) P Q
    | each {input : Ref context (List a)} {captures : Capture context captured}
        {body : Graph schema models scope app (a :: captured) outputs}
        {P : Values context → Prop} {Q : Values context → List (Values outputs) → Prop}
        {relation : Values context → a → Values outputs → Prop}
        (bodyProof : ∀ values, P values → ∀ row ∈ input.read values,
          GraphProof contracts body (fun args => args = (row, captures.read values)) (relation values row))
        (close : ∀ values, P values → ∀ results,
          RelatedLists (relation values) (input.read values) results → Q values results) :
        NodeProof contracts (.each input captures body) P Q
    | mapRows {input : Ref context (Gathered a)} {captures : Capture context captured}
        {body : Graph schema models scope app (a :: captured) outputs} {result : Ref outputs b}
        {P : Values context → Prop} {Q : Values context → Gathered b → Prop}
        {relation : (values : Values context) → RowIndex (input.read values).width → b → Prop}
        (bodyProof : ∀ values, P values → ∀ index,
          GraphProof contracts body
            (fun args => args = ((input.read values).getValue index, captures.read values))
            (fun outputs => relation values index (result.read outputs)))
        (close : ∀ values, P values → ∀ answers,
          (∀ index, relation values index (answers index)) →
          Q values ⟨(input.read values).count, (input.read values).width, answers⟩) :
        NodeProof contracts (.mapRows input captures body result) P Q
end

theorem graph_proof_sound {input output : List Type}
    {graph : Graph schema models scope app input output} {contracts : Contracts schema models scope app}
    {P : Values input → Prop} {Q : Values output → Prop} (proof : GraphProof contracts graph P Q)
    (backend : Meanings schema models scope app) (satisfies : BackendSatisfies contracts backend)
    (values : Values input) (pre : P values) : Q (denoteGraph backend graph values) := by
  revert values
  induction proof using GraphProof.rec
      (motive_2 := fun node P Q _ => ∀ values, P values → Q values (denoteNode backend node values)) with
  | nil close => exact close
  | snoc prior step close priorIH stepIH =>
    intro values pre
    exact close _ (priorIH values pre) _ (stepIH _ (priorIH values pre))
  | literal close | map close | pair close | gather close | scatter close | fromLists close =>
    exact close _ ‹_›
  | call ready close =>
    rename_i values pre
    exact close values pre _ (satisfies _ _ _ _ (ready values pre))
  | vectorLoad ready close =>
    rename_i values pre
    exact close values pre _ (fun index => satisfies _ _ _ _ (ready values pre index))
  | each bodyProof close ih =>
    rename_i values pre
    apply close values pre
    exact forall2_mapped _ _ _ (fun row member => ih values pre row member _ rfl)
  | mapRows bodyProof close ih =>
    rename_i values pre
    exact close values pre _ (fun index => ih values pre index _ rfl)

theorem node_proof_sound {context : List Type} {result : Type}
    {node : Node schema models scope app context result} {contracts : Contracts schema models scope app}
    {P : Values context → Prop} {Q : Values context → result → Prop} (proof : NodeProof contracts node P Q)
    (backend : Meanings schema models scope app) (satisfies : BackendSatisfies contracts backend)
    (values : Values context) (pre : P values) : Q values (denoteNode backend node values) := by
  have graphProof : GraphProof contracts (.snoc .nil node) P (fun values => Q values.2 values.1) :=
    .snoc (.nil (fun _ h => h)) proof (fun _ _ _ h => h)
  exact graph_proof_sound graphProof backend satisfies values pre

theorem related_lists_length (proof : RelatedLists relation left right) : left.length = right.length := by
  induction proof with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- A captured region preserves row identity, order and captured values. -/
theorem identity_region_certificate (contracts : Contracts schema models scope app)
    (input : Ref context (List a)) (captures : Capture context captured) :
    NodeProof contracts (.each input captures .nil) (fun _ => True)
      (fun values results => RelatedLists (fun row output => output = (row, captures.read values))
        (input.read values) results) := by
  apply NodeProof.each
  · intro values _ row _
    exact .nil (fun _ eq => eq)
  · exact fun _ _ _ h => h

/-- Gathered regions preserve both coordinates and values; no flattening loses provenance. -/
theorem identity_rows_certificate (contracts : Contracts schema models scope app)
    (input : Ref context (Gathered a)) (captures : Capture context captured) :
    NodeProof contracts (.mapRows input captures .nil .here) (fun _ => True)
      (fun values result => result = input.read values) := by
  apply NodeProof.mapRows (relation := fun values index result => result = (input.read values).getValue index)
  · intro values _ index
    exact .nil (fun outputs eq => congrArg Prod.fst eq)
  · intro values _ answers pointwise
    have eq := funext pointwise
    subst answers
    rfl

def CallReady (contracts : Contracts schema models scope app)
    (node : Node schema models scope app context result) (P : Values context → Prop) : Prop :=
  match node with
  | .call field token parent args => ∀ values, P values →
      contracts.pre field (token.read values) (parent.read values) (args.read values)
  | _ => True

theorem node_certificate_ready (proof : NodeProof contracts node P Q) : CallReady contracts node P := by
  cases proof <;> first | assumption | trivial

end GraphQL.Plan

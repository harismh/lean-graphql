import GraphQL.Plan.Specifications
import GraphQL.Plan.ResultSpec
import GraphQL.Plan.Judgment

namespace GraphQL.Plan.BoundedExample

/-- An independent policy: total result cardinality, without any tenant model. -/
abbrev schema : Schema := ⟨1, fun _ => [⟨"zeros", .unit, .list .int⟩]⟩
abbrev models : Fin 1 → Type := fun _ => Nat
def field : FieldId schema 0 := ⟨⟨0, by decide⟩⟩
def contracts : Contracts schema models Nat Empty where
  pre := fun {_} _ _ _ _ => True
  post := fun {_} f limit _ _ => match f with
    | ⟨⟨0, _⟩⟩ => fun result => match result with
      | .ok values => values.length ≤ limit
      | .error _ => False
    | ⟨⟨n + 1, h⟩⟩ => False.elim (by simp [schema] at h)
  compatible := fun {_} _ _ {_} _ => True

def backend : Meanings schema models Nat Empty :=
  fun {_} f limit requested _ => match f with
  | ⟨⟨0, _⟩⟩ => .ok (List.replicate (min requested limit) (0 : Int))
  | ⟨⟨n + 1, h⟩⟩ => False.elim (by simp [schema] at h)

theorem backend_bounded : BackendSatisfies contracts backend := by
  intro object f limit requested args _
  rcases f with ⟨⟨index, bound⟩⟩
  have eq : index = 0 := by simp [schema] at bound; omega
  subst index
  change (List.replicate (min requested limit) (0 : Int)).length ≤ limit
  simpa only [List.length_replicate] using Nat.min_le_right requested limit

def plan : Graph schema models Nat Empty [Nat, Nat, Unit] [Outcome Empty (List Int), Nat, Nat, Unit] :=
  .snoc .nil (.call field (.there .here) .here (.there (.there .here)))

theorem plan_certificate : GraphProof contracts plan (fun _ => True)
    (fun values => match values.1 with | .ok rows => rows.length ≤ values.2.2.1 | .error _ => False) := by
  apply GraphProof.snoc (.nil (fun _ h => h))
    (NodeProof.call (fun _ _ => True.intro) (fun _ _ _ h => h))
  intro values _ result h
  cases result <;> exact h

theorem plan_bounded (requested limit : Nat) :
    match (denoteGraph backend plan (requested, limit, (), ())).1 with
    | .ok rows => rows.length ≤ limit
    | .error _ => False :=
  graph_proof_sound plan_certificate backend backend_bounded _ True.intro

def scalarSpec : ResultSpec Empty Int := ⟨fun value => value = 0, fun _ => False⟩

theorem completed_bound (requested limit : Nat) :
    (ResultSpec.mk (fun rows : List Int => rows.length ≤ limit ∧ ∀ x ∈ rows, x = 0)
      (fun _ : Empty => False)).Satisfies
      (Completion.collect ((List.replicate (min requested limit) (0 : Int)).map
        (fun value => Completion.ok value []))) := by
  apply result_collect_bound scalarSpec
  · simp only [List.length_map, List.length_replicate]
    exact Nat.min_le_right requested limit
  · intro row member
    obtain ⟨value, included, rfl⟩ := List.mem_map.mp member
    apply result_leaf scalarSpec value
    exact (List.mem_replicate.mp included).2

/-- Elementwise correctness does not establish a whole-list cardinality bound. -/
theorem elementwise_is_insufficient :
    (∀ x ∈ ([0, 0] : List Int), scalarSpec.valueValid x) ∧ ¬ ([0, 0] : List Int).length ≤ 1 := by
  simp [scalarSpec]

inductive ResponseRule : Nat → List (Nat × List Int) → List Int → Prop where
  | empty : ResponseRule limit [] []
  | cons : ResponseRule (limit + 1) [(limit, rest)] (0 :: rest)

theorem response_rules_preserve (limit : Nat) (premises : List (Nat × List Int)) (rows : List Int)
    (children : ∀ pair ∈ premises, pair.2.length ≤ pair.1)
    (law : ResponseRule limit premises rows) : rows.length ≤ limit := by
  cases law with
  | empty => exact Nat.zero_le _
  | cons => exact Nat.succ_le_succ (children _ List.mem_cons_self)

theorem response_bound (proof : ResponseJudgment ResponseRule limit id rows) : rows.length ≤ limit := by
  obtain ⟨values, derivation, rfl⟩ := proof
  exact judgment_sound ResponseRule (fun limit rows => rows.length ≤ limit) response_rules_preserve derivation

theorem bounded_response_example : ResponseJudgment ResponseRule 2 id [0, 0] := by
  refine ⟨[0, 0], ?_, rfl⟩
  apply Judgment.step [(1, [0])]
  · intro pair member
    have eq : pair = (1, [0]) := List.mem_singleton.mp member
    subst pair
    apply Judgment.step [(0, [])]
    · intro pair member
      have eq : pair = (0, []) := List.mem_singleton.mp member
      subst pair
      exact .step [] (by simp) .empty
    · exact .cons
  · exact .cons

theorem replicate_judgment (count limit : Nat) (bound : count ≤ limit) :
    Judgment ResponseRule limit (List.replicate count (0 : Int)) := by
  induction count generalizing limit with
  | zero => exact .step [] (by simp) .empty
  | succ count ih =>
    cases limit with
    | zero => omega
    | succ limit =>
      apply Judgment.step [(limit, List.replicate count 0)]
      · intro pair member
        have eq := List.mem_singleton.mp member
        subst pair
        exact ih limit (by omega)
      · exact .cons

def runRows (requested limit : Nat) : List Int :=
  match (denoteGraph backend plan (requested, limit, (), ())).1 with
  | .ok rows => rows
  | .error _ => []

/-- The same actual graph result flows through completion and the response judgment. -/
theorem program_completion_response (requested limit : Nat) :
    let rows := runRows requested limit
    (ResultSpec.mk (fun rows : List Int => rows.length ≤ limit ∧ ∀ x ∈ rows, x = 0)
      (fun _ : Empty => False)).Satisfies (Completion.collect (rows.map (fun x => .ok x []))) ∧
    ResponseJudgment ResponseRule limit id rows := by
  exact ⟨completed_bound requested limit,
    ⟨_, replicate_judgment _ _ (Nat.min_le_right requested limit), rfl⟩⟩

end GraphQL.Plan.BoundedExample

import Std

namespace GraphQL.Plan

/-- A law rule may inspect child results; every child requires its own derivation.
Rules describe allowed observations independently of any evaluator. -/
inductive Judgment (rule : goal → List (goal × value) → value → Prop) : goal → value → Prop where
  | step (premises : List (goal × value))
      (children : ∀ pair ∈ premises, Judgment rule pair.1 pair.2)
      (law : rule target premises result) : Judgment rule target result

def ResponseJudgment (rule : goal → List (goal × value) → value → Prop)
    (root : goal) (finish : value → response) (output : response) : Prop :=
  ∃ value, Judgment rule root value ∧ finish value = output

theorem judgment_sound (rule : goal → List (goal × value) → value → Prop)
    (property : goal → value → Prop)
    (close : ∀ target premises result,
      (∀ pair ∈ premises, property pair.1 pair.2) → rule target premises result → property target result)
    (proof : Judgment rule target result) : property target result := by
  induction proof with
  | step premises children law ih => exact close _ premises _ ih law

theorem response_judgment_sound (rule : goal → List (goal × value) → value → Prop)
    (property : goal → value → Prop)
    (close : ∀ target premises result,
      (∀ pair ∈ premises, property pair.1 pair.2) → rule target premises result → property target result)
    (finish : value → response) (conclusion : response → Prop)
    (bridge : ∀ value, property root value → conclusion (finish value))
    (proof : ResponseJudgment rule root finish output) : conclusion output := by
  obtain ⟨value, derivation, rfl⟩ := proof
  exact bridge value (judgment_sound rule property close derivation)

theorem judgment_leaf (law : rule target [] result) : Judgment rule target result :=
  .step [] (by simp) law

theorem judgment_unary (child : Judgment rule childGoal childValue)
    (law : rule target [(childGoal, childValue)] result) : Judgment rule target result := by
  apply Judgment.step _ _ law
  intro pair member
  have eq := List.mem_singleton.mp member
  subst pair
  exact child

theorem judgment_binary (left : Judgment rule leftGoal leftValue) (right : Judgment rule rightGoal rightValue)
    (law : rule target [(leftGoal, leftValue), (rightGoal, rightValue)] result) : Judgment rule target result := by
  apply Judgment.step _ _ law
  intro pair member
  rcases List.mem_cons.mp member with eq | member
  · subst pair; exact left
  · have eq := List.mem_singleton.mp member
    subst pair; exact right

end GraphQL.Plan

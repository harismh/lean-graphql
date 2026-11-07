import Example.Tenant.LoweringCorrectness
import Example.Tenant.WaveExample
import Example.Tenant.S0Proofs
import GraphQL.Plan.CallDenotation

namespace Example.Tenant.S1Proofs
open Planning Checks GraphQL.Plan

def success : IR.Checked .query query := (IR.lower .query query).get (by decide)
def nullable : IR.Checked .query S0Proofs.nullableQuery :=
  (IR.lower .query S0Proofs.nullableQuery).get (by decide)
def required : IR.Checked .query S0Proofs.requiredQuery :=
  (IR.lower .query S0Proofs.requiredQuery).get (by decide)

theorem compiled_success : plannedResponse snapshot caller success = S0Proofs.successResponse := rfl

theorem compiled_nullable_bubble :
    plannedResponse snapshot caller nullable = S0Proofs.nullableResponse := rfl

theorem compiled_required_bubble :
    plannedResponse snapshot caller required = S0Proofs.requiredResponse := rfl

theorem compiled_success_authorized :
    Spec.AuthorizedResponse snapshot caller query (plannedResponse snapshot caller success) :=
  planned_authorized success (by decide)

theorem compiled_required_conforms :
    Spec.Conforms S0Proofs.requiredQuery (plannedResponse snapshot caller required) :=
  planned_conforms required (by decide)

theorem prepared_success :
    (prepare snapshot (IR.toTemplate success.val)).map
      (fun operation => Spec.envelope (operationDenotes (meanings snapshot) operation () caller [])) =
      some S0Proofs.successResponse := rfl

theorem empty_template_rejected : prepare snapshot .nil = none := rfl

/-- Argument errors are pure nodes: neither the backend nor its result is used. -/
theorem argument_error_skips_backend (backend : Backend snapshot) (key : String) :
    denoteNode backend
      (callNode IR.Branch.project (some .argument)
        (Ref.here : Ref [Principal, Unit, String] Principal) (.there .here) (.there (.there .here)))
      (caller, (), key, ()) = .error (.framework .argument) := rfl

theorem duplicate_and_empty_rows :
    (scatter (gather (Nested.ofLists ([["same", "same"], [], ["other"]])))).toLists =
      [["same", "same"], [], ["other"]] := gather_scatter_lists _

theorem filtered_positions (rows : List (List α)) (keep : α → Bool) :
    (scatter (gather (Nested.ofLists (rows.map (List.filter keep))))).toLists =
      rows.map (List.filter keep) := gather_scatter_lists _

def outcomes : List (List (Outcome ApplicationError (Option String))) :=
  [[.ok (some "same"), .ok none, .error (.application .unavailable)], [], [.ok (some "same")]]

theorem missing_and_error_positions :
    (scatter (gather (Nested.ofLists outcomes))).toLists = outcomes := gather_scatter_lists _

theorem reordered_scatter_rejected :
    (scatter (gather (Nested.ofLists ([[1, 2], [3]] : List (List Nat))))).toLists ≠
      [[2, 1], [3]] := by rw [gather_scatter_lists]; decide

theorem wrong_parent_rejected :
    (scatter (gather (Nested.ofLists ([[1], [2]] : List (List Nat))))).toLists ≠
      [[2], [1]] := by rw [gather_scatter_lists]; decide

theorem materialized_order :
    (gather (Nested.ofLists ([[1, 1], [], [2, 3]] : List (List Nat)))).materialize.toList =
      [1, 1, 2, 3] := by rw [materialize_gather, nested_lists_roundtrip]; rfl

theorem omitted_is_not_null : (Input.omitted : Input String) ≠ .null := omitted_ne_null

/-- A body consumes a precomputed result rather than reissuing its field call. -/
def preloadedBody (s : Snapshot) :
    TenantGraph s [Outcome ApplicationError String] [Outcome ApplicationError String] := .nil

def preloadedOutput (s : Snapshot) : Output s (preloadedBody s) :=
  .leaf IR.Leaf.projectTitle ⟨.here⟩ .empty

structure VectorExample (s : Snapshot) where
  outputs : List Type
  graph : TenantGraph s [List (Occurrence s.projects), Principal] outputs
  output : Output s graph

/-- Representability witness, not an optimizer: gather/load runs outside the child
body, whose output plan receives the precomputed result through its typed input. -/
def vectorExample (s : Snapshot) : VectorExample s :=
  let start : TenantGraph s [List (Occurrence s.projects), Principal] _ := .nil
  let lists := start.snoc (.map (fun rows : List (Occurrence s.projects) =>
    [rows.map (fun row => (row, ()))]) .here)
  let nested := lists.snoc (.fromLists .here)
  let gathered := nested.snoc (.gather .here)
  let loaded := gathered.snoc (.vectorLoad (leafId IR.Leaf.projectTitle)
    (gathered.inputs.rename (.there .here)) .here)
  let flat := loaded.snoc (.map (fun rows => rows.materialize.toList) .here)
  let frames := flat.snoc (.each .here .nil (preloadedBody s))
  let branded := frames.snoc (.map (fun values => values.map
    (fun value => (⟨value⟩ : Frame (preloadedBody s)))) .here)
  let result := branded.snoc (.map (fun rows => (Except.ok rows :
    Outcome ApplicationError (List (Occurrence s.projects)))) (branded.inputs.rename .here))
  ⟨_, result, .object IR.Branch.projects ⟨.here⟩ (preloadedBody s)
    ⟨.there .here⟩ (preloadedOutput s) .empty⟩

theorem precomputed_results_reach_output :
    Spec.envelope (render (vectorExample snapshot).output
      (runDenotation (meanings snapshot) (vectorExample snapshot).graph
        (projectOccurrences snapshot caller, caller, ())) []) = S0Proofs.successResponse := rfl

/-- Deliberately incorrect reconstructions for checking the strength of the laws. -/
def chunks : List Nat → List α → List (List α)
  | [], _ => []
  | width :: widths, values => values.take width :: chunks widths (values.drop width)

def badParentScatter (rows : Gathered Nat) : Nested Nat :=
  Nested.ofLists (chunks (List.ofFn rows.width).reverse rows.materialize.toList)

def insertKey (key : Nat) : List Nat → List Nat
  | [] => [key]
  | next :: rest => if key ≤ next then key :: next :: rest else next :: insertKey key rest

def sortKeys : List Nat → List Nat
  | [] => []
  | head :: tail => insertKey head (sortKeys tail)

def badKeyOrderScatter (rows : Gathered Nat) : Nested Nat :=
  Nested.ofLists (chunks (List.ofFn rows.width)
    (sortKeys rows.materialize.toList))

def badScatterFixture : Nested Nat := Nested.ofLists [[2, 2], [], [1]]

theorem wrong_parent_algorithm_fails : badParentScatter (gather badScatterFixture) ≠ badScatterFixture := by
  intro h
  have unequal : (badParentScatter (gather badScatterFixture)).toLists ≠ badScatterFixture.toLists := by decide
  exact unequal (congrArg Nested.toLists h)

theorem key_order_algorithm_fails : badKeyOrderScatter (gather badScatterFixture) ≠ badScatterFixture := by
  intro h
  have unequal : (badKeyOrderScatter (gather badScatterFixture)).toLists ≠ badScatterFixture.toLists := by decide
  exact unequal (congrArg Nested.toLists h)

end Example.Tenant.S1Proofs

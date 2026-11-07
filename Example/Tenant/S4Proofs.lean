import Example.Tenant.S3Proofs
import Example.Tenant.FaultShape
import Example.Tenant.SuccessfulExecution
import Example.Tenant.View
import GraphQL.Plan.ItemsExample
import GraphQL.Plan.ListCompletion

namespace Example.Tenant.S4Proofs
open GraphQL.Plan Planning

def request : Binding.Request := ⟨Checks.snapshot, Checks.caller⟩

def titleFaults : Meanings schema Binding.carriers Binding.Request ApplicationError :=
  fun {_} field request parent args =>
    if field.decl.name == "title" then .error (.framework .exhausted)
    else Contract.Expected field request parent args

theorem title_faults_permitted : BackendSatisfies Fault.contracts titleFaults := by
  intro object field request parent args pre
  dsimp only [Fault.contracts, titleFaults]
  split
  · exact Or.inr ⟨.exhausted, rfl⟩
  · exact Or.inl ⟨rfl, Contract.expected_owned field request parent args⟩

theorem filtered_error_position :
    runMachine (denoteCall titleFaults) (Runtime.execute request S1Proofs.success) =
      ⟨.null, [⟨.framework .exhausted, [.field "projects", .index 0, .field "title"]⟩]⟩ := rfl

theorem fault_response_authorized : Spec.AuthorizedResponse request.snapshot request.principal Checks.query
    (runMachine (denoteCall titleFaults) (Runtime.execute request S1Proofs.success)) :=
  Fault.permitted_driver_authorized request S1Proofs.success (by decide) _
    (call_contract Fault.contracts titleFaults title_faults_permitted)

theorem fault_response_conforms : Spec.Conforms Checks.query
    (runMachine (denoteCall titleFaults) (Runtime.execute request S1Proofs.success)) :=
  Fault.authorized_conforms fault_response_authorized

def repeatedRequest : Binding.Request :=
  ⟨⟨[Checks.ownedProject, Checks.ownedProject], []⟩, Checks.caller⟩

theorem repeated_faults_preserve_multiplicity :
    (runMachine (denoteCall titleFaults) (Runtime.execute repeatedRequest S1Proofs.success)).errors =
      [⟨.framework .exhausted, [.field "projects", .index 0, .field "title"]⟩,
       ⟨.framework .exhausted, [.field "projects", .index 1, .field "title"]⟩] := rfl

theorem tenant_view_run : Runtime.run (Binding.adapt Binding.application) (View.request request) S1Proofs.success =
    Runtime.run (Binding.adapt Binding.application) request S1Proofs.success :=
  View.run_tenant_view _ Binding.application_agreement _ _

def itemPath : ItemsExample.Path := [Sum.inl "items"]

theorem items_cap_in_execution :
    runMachine (denoteCall ItemsExample.backend)
      (ItemsExample.execute (List.replicate 150 "item") (.value 1000) itemPath) =
      .ok (some (List.replicate 100 "item")) [] := by
  rw [ItemsExample.run_execution]
  change Completion.boundary none false (ItemsExample.complete itemPath
    (.ok ((List.replicate 150 "item").take 100))) = _
  rw [ItemsExample.complete_success]
  rfl

theorem items_negative_in_execution :
    runMachine (denoteCall ItemsExample.backend)
      (ItemsExample.execute ["item"] (.value (-1)) itemPath) =
      .bubble [(.application .badLimit, itemPath)] := rfl

def limitFaults : Meanings ItemsExample.schema ItemsExample.models (List String) ItemsExample.Error :=
  fun {_} _ _ _ _ => .error (.framework .internal)

theorem limit_faults_permitted : BackendSatisfies ItemsExample.contracts limitFaults := by
  intro object field rows parent args _
  rcases field with ⟨⟨index, valid⟩⟩
  have eq : index = 0 := by simp [ItemsExample.schema] at valid; omega
  subst index
  trivial

theorem items_fault_bound :
    (ItemsExample.specification (.value 2) itemPath false).Satisfies
      (runMachine (denoteCall limitFaults) (ItemsExample.execute ["a", "b", "c"] (.value 2) itemPath)) :=
  ItemsExample.permitted_driver_bound _ (call_contract _ _ limit_faults_permitted) _ _ _ _

theorem required_list_required_item :
    completeList false false ([.bubble ["error"]] : List (Completion String (Option Nat))) = .bubble ["error"] := rfl

theorem nullable_list_required_item :
    completeList true false ([.bubble ["error"]] : List (Completion String (Option Nat))) = .ok none ["error"] := rfl

theorem required_list_nullable_item :
    completeList false true ([.bubble ["error"]] : List (Completion String (Option Nat))) = .ok (some [none]) ["error"] := rfl

theorem nullable_list_nullable_item :
    completeList true true ([.bubble ["error"]] : List (Completion String (Option Nat))) = .ok (some [none]) ["error"] := rfl

theorem unbounded_items_rejected :
    ¬ ItemsExample.ResultAllowed (.value 1) (.ok ["a", "b"]) := by
  intro proof
  obtain ⟨bound, selected, length⟩ := proof
  have eq : 1 = bound := Except.ok.inj selected
  subst bound
  contradiction

theorem swallowed_required_fault_rejected :
    ¬ (ItemsExample.specification (.value 1) itemPath false).Satisfies (.ok none []) := by
  intro proof
  exact Bool.noConfusion proof.1

def varyingMeanings (counter : Nat) : Meanings schema Binding.carriers Binding.Request ApplicationError :=
  fun {_} field request parent args =>
    if counter = 2 ∧ field.decl.name = "title" then .error (.framework .exhausted)
    else Contract.Expected field request parent args

def varyingResolver (counter : Nat) (call : Call schema Binding.carriers Binding.Request) : Answer ApplicationError call × Nat :=
  (denoteCall (varyingMeanings counter) call, counter + 1)

theorem varying_resolver_permitted (counter : Nat) (call : Call schema Binding.carriers Binding.Request)
    (pre : Fault.contracts.Pre call) : Fault.contracts.Post call (varyingResolver counter call).1 := by
  apply call_contract Fault.contracts (varyingMeanings counter) _ call pre
  intro object field request parent args _
  dsimp only [Fault.contracts, varyingMeanings]
  split
  · exact Or.inr ⟨.exhausted, rfl⟩
  · exact Or.inl ⟨rfl, Contract.expected_owned field request parent args⟩

theorem differing_duplicate_outcomes :
    (runStateMachine varyingResolver (Runtime.execute repeatedRequest S1Proofs.success) 0).1 =
      ⟨.null, [⟨.framework .exhausted, [.field "projects", .index 1, .field "title"]⟩]⟩ := rfl

theorem stateful_fault_authorized :
    Spec.AuthorizedResponse repeatedRequest.snapshot repeatedRequest.principal Checks.query
      (runStateMachine varyingResolver (Runtime.execute repeatedRequest S1Proofs.success) 0).1 :=
  sat_run_state varyingResolver varying_resolver_permitted _
    (Fault.execution_authorized repeatedRequest S1Proofs.success (by decide)) 0

def swallowedExecution := (Runtime.execute request S1Proofs.success).bind
  (fun response => GraphQL.Machine.done ({ response with errors := [] } : Spec.Response))

theorem mutated_renderer_rejected :
    ¬ Spec.Conforms Checks.query (runMachine (denoteCall titleFaults) swallowedExecution) :=
  Spec.null_without_error_rejected Checks.query

theorem legitimate_null_element :
    (listSpec (fun _ : Nat => True) (fun _ : String => True) 1 false true).Satisfies
      (completeList false true [.ok none []]) := by
  apply list_completion_contract
  · decide
  · intro row member
    have eq := List.mem_singleton.mp member
    subst row
    exact ⟨rfl, by simp⟩

end Example.Tenant.S4Proofs

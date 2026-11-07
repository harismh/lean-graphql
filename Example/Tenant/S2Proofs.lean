import Example.Tenant.BindingBridge
import Example.Tenant.S1Proofs

namespace Example.Tenant.S2Proofs
open GraphQL.Plan Binding

def request : Request := ⟨Checks.snapshot, Checks.caller⟩
def witness : Project := ⟨"identifier", 1, "display title", []⟩

/-- Both swapped functions have the right Lean argument and result types. -/
def swapped : ResolverRecord := { application with
  projectId := ⟨projectTitleBinding.single, none⟩
  projectTitle := ⟨projectIdBinding.single, none⟩ }

theorem swapped_adapter_rejected : ¬ BindingAgreement independentBindings (adapt swapped) := by
  intro h
  have wrong := adapter_single_agreement independentBindings (adapt swapped) h
    1 ⟨1, by decide⟩ request witness ()
  change (Except.ok "identifier" : Outcome ApplicationError String) = .ok "display title" at wrong
  exact (by decide : ("identifier" : String) ≠ "display title") (Except.ok.inj wrong)

def otherRequest : Request := ⟨⟨[], []⟩, Checks.caller⟩

theorem equal_keys_do_not_allow_cross_request_reuse :
    taskProjectKey.key ⟨S0Proofs.consistentSnapshot, Checks.caller⟩ ⟨"t", 1, "task", "p"⟩ () =
      taskProjectKey.key otherRequest ⟨"t", 1, "task", "p"⟩ () ∧
    taskProjectSingle ⟨S0Proofs.consistentSnapshot, Checks.caller⟩ ⟨"t", 1, "task", "p"⟩ () ≠
      taskProjectSingle otherRequest ⟨"t", 1, "task", "p"⟩ () := by
  constructor
  · rfl
  · intro h; cases h

def plainBatch : BatchCapability (models := carriers) Binding.taskProject taskProjectSingle :=
  { taskProjectBatch with deduplication := none }

theorem plain_batch_has_no_deduplication : plainBatch.deduplication = none := rfl

theorem missing_capability_uses_single_meaning :
    answerBinding (adapt application) (.batch projectTitle request #v[(witness, ())]) =
      #v[(Except.ok "display title" : Outcome ApplicationError String)] := by
  rw [answer_binding_exact]
  apply Vector.ext
  intro i hi
  have zero : i = 0 := by omega
  subst i
  exact batch_position (Adapter.meanings (adapt application)) projectTitle request #v[(witness, ())] ⟨0, by decide⟩

theorem batch_preserves_duplicates_and_failures :
    answerBinding (adapt application)
      (.batch Binding.taskProject request #v[(Checks.ownedTask, ()), (Checks.ownedTask, ())]) =
      #v[(Except.error (.application .unavailable) : Outcome ApplicationError Project),
         .error (.application .unavailable)] := by
  rw [answer_binding_exact]
  apply Vector.ext
  intro i hi
  have pos := batch_position (Adapter.meanings (adapt application)) Binding.taskProject request
    #v[(Checks.ownedTask, ()), (Checks.ownedTask, ())] ⟨i, hi⟩
  have either : i = 0 ∨ i = 1 := by omega
  rcases either with rfl | rfl <;> exact pos

theorem batch_and_key_are_anchored :
    (adapt application Binding.taskProject).batch = some taskProjectBatch ∧
      taskProjectBatch.deduplication = some taskProjectKey := ⟨rfl, rfl⟩

def wrongSchema : IndexedSchema demoAst :=
  { indexedSchema with fields := fun owner =>
    if owner.val = 1 then [⟨"title", .unit, .string⟩, ⟨"id", .unit, .string⟩,
      ⟨"tasks", .unit, .list (.object 2)⟩] else indexedSchema.fields owner }

theorem same_typed_schema_swap_rejected : ¬ Represents demoAst wrongSchema := by decide +kernel

theorem optional_input_distinction :
    presenceToInput (GraphQL.Presence.missing : GraphQL.Presence String) ≠
      presenceToInput (.null : GraphQL.Presence String) := by decide

theorem framework_failure_roundtrip :
    fromOutcome (toOutcome (.error (.framework .exhausted) : Except (Example.Tenant.PublicError ApplicationError) String)) =
      .error (.framework .exhausted) := rfl

theorem constant_key_cannot_be_sufficient :
    ¬ (∀ (context : Request) (left right : Task),
      taskProjectSingle context left () = taskProjectSingle context right ()) := by
  intro h
  have result := congrArg (fun outcome => outcome.toOption.map Project.id)
    (h ⟨WaveExample.multiSnapshot, Checks.caller⟩
      ⟨"t", 1, "task", "p1"⟩ ⟨"u", 1, "other", "p2"⟩)
  exact (by decide : (some "p1" : Option String) ≠ some "p2") result

def unsupportedAst : GraphQL.Schema := ⟨[
  ⟨"Query", .object, [⟨"value", .named "String" true,
    [⟨"values", .list (.named "String" true) true⟩]⟩], [], []⟩], "Query"⟩

theorem unsupported_input_profile_rejected : ¬ WellFormedSchema unsupportedAst := by decide +kernel

/-- Mutating wrapper code cannot mutate the independent target along with it. -/
def swappedIdWrapper : FieldBinding Binding.projectId carriers Request ApplicationError :=
  ⟨fun request parent args => toOutcome (resolveProjectTitle request parent args), none⟩

def wrapperSwapped : ResolverRecord := { application with projectId := swappedIdWrapper }

theorem swapped_wrapper_rejected : ¬ BindingAgreement independentBindings (adapt wrapperSwapped) := by
  intro h
  have wrong := adapter_single_agreement independentBindings (adapt wrapperSwapped) h
    1 ⟨0, by decide⟩ request Checks.ownedProject ()
  change (Except.ok "public" : Outcome ApplicationError String) = .ok "shared" at wrong
  exact (by decide : ("public" : String) ≠ "shared") (Except.ok.inj wrong)

theorem swapped_wrapper_breaks_semantic_anchor :
    Adapter.meanings (adapt wrapperSwapped) Binding.projectId request Checks.ownedProject () ≠
      convertOutcome Binding.projectId.decl.output (transport Checks.snapshot)
        (Planning.meanings Checks.snapshot (Planning.leafId IR.Leaf.projectId)
          Checks.caller Checks.ownedOccurrence ()) := by
  intro wrong
  change (Except.ok "public" : Outcome ApplicationError String) = .ok "shared" at wrong
  exact (by decide : ("public" : String) ≠ "shared") (Except.ok.inj wrong)

end Example.Tenant.S2Proofs

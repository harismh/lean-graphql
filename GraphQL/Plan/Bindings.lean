import GraphQL.Plan.SchemaEvidence
import GraphQL.Plan.CallDenotation

namespace GraphQL.Plan

variable {scope app : Type} {ast : GraphQL.Schema} {checked : CheckedIndexed ast}

/-- Equal keys justify reuse only for the very same deterministic single backend
and request scope. This is not inferred from a field name or a postcondition. -/
structure SufficientKey (field : FieldId schema owner)
    (single : scope → models owner → field.Args → Outcome app (field.Out models)) where
  Key : Type
  equal : DecidableEq Key
  key : scope → models owner → field.Args → Key
  sufficient : ∀ context left leftArgs right rightArgs,
    key context left leftArgs = key context right rightArgs →
      single context left leftArgs = single context right rightArgs

/-- Semantic exactness only. No physical-request or reduced-call-count claim is
provided by this record; the S4b strategy must separately establish its cost bound. -/
structure BatchCapability (field : FieldId schema owner)
    (single : scope → models owner → field.Args → Outcome app (field.Out models)) where
  run : scope → {n : Nat} → Vector (models owner × field.Args) n →
    Vector (Outcome app (field.Out models)) n
  exact : ∀ context {n} (inputs : Vector (models owner × field.Args) n) i,
    (run context inputs).get i = single context (inputs.get i).1 (inputs.get i).2
  deduplication : Option (SufficientKey field single) := none

structure FieldBinding (field : FieldId schema owner) (models : Fin schema.objectCount → Type)
    (scope app : Type) where
  single : scope → models owner → field.Args → Outcome app (field.Out models)
  batch : Option (BatchCapability field single) := none

/-- Canonical AST coordinates, fixed independently of an adapter or its metadata. -/
abbrev BindingsByField (checked : CheckedIndexed ast) (models : Fin ast.types.length → Type)
    (scope app : Type) :=
  (owner : Fin ast.types.length) → (field : CanonicalField ast owner) →
    FieldBinding (checked.field owner field) models scope app

abbrev Adapter (schema : Schema) (models : Fin schema.objectCount → Type) (scope app : Type) :=
  {owner : Fin schema.objectCount} → (field : FieldId schema owner) → FieldBinding field models scope app

def adaptBindings (bindings : BindingsByField checked models scope app) :
    Adapter checked.indexed.schema models scope app :=
  fun field => bindings _ (checked.coordinate field)

/-- Equality includes the backend, optional batch capability and its key/law, not
just a separately generated dispatch-name table. -/
def BindingAgreement (bindings : BindingsByField checked models scope app)
    (adapter : Adapter checked.indexed.schema models scope app) : Prop :=
  ∀ owner (field : CanonicalField _ owner), adapter (checked.field owner field) = bindings owner field

theorem adapt_bindings_agreement (bindings : BindingsByField checked models scope app) :
    BindingAgreement bindings (adaptBindings bindings) := by intro owner field; rfl

def Adapter.meanings (adapter : Adapter schema models scope app) : Meanings schema models scope app :=
  fun field => (adapter field).single

theorem adapter_single_agreement (bindings : BindingsByField checked models scope app)
    (adapter : Adapter checked.indexed.schema models scope app) (h : BindingAgreement bindings adapter)
    (owner : Fin ast.types.length) (field : CanonicalField ast owner) context parent args :
    adapter.meanings (checked.field owner field) context parent args =
      (bindings owner field).single context parent args := by
  unfold Adapter.meanings
  exact congrArg (fun binding => binding.single context parent args) (h owner field)

def answerBinding (adapter : Adapter schema models scope app) :
    (call : Call schema models scope) → Answer app call
  | .one field context parent args => (adapter field).single context parent args
  | .batch field context inputs => match (adapter field).batch with
    | some capability => capability.run context inputs
    | none => inputs.map (fun (parent, args) => (adapter field).single context parent args)

theorem answer_binding_exact (adapter : Adapter schema models scope app)
    (call : Call schema models scope) :
    answerBinding adapter call = denoteCall adapter.meanings call := by
  cases call with
  | one field context parent args => rfl
  | batch field context inputs =>
    simp only [answerBinding]
    split
    · rename_i capability h
      apply Vector.ext
      intro i hi
      have eq := capability.exact context inputs ⟨i, hi⟩
      simpa [denoteCall, Adapter.meanings, Vector.get, Fin.cast] using eq
    · rfl

theorem batch_postconditions {schema : Schema} {owner : Fin schema.objectCount}
    {models : Fin schema.objectCount → Type} {field : FieldId schema owner}
    {single : scope → models owner → field.Args → Outcome app (field.Out models)}
    (capability : BatchCapability field single)
    (post : models owner → field.Args → Outcome app (field.Out models) → Prop)
    (valid : ∀ parent args, post parent args (single context parent args))
    (inputs : Vector (models owner × field.Args) n) :
    ∀ i, post (inputs.get i).1 (inputs.get i).2 ((capability.run context inputs).get i) := by
  intro i
  rw [capability.exact]
  exact valid _ _

end GraphQL.Plan

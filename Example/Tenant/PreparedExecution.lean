import Example.Tenant.InputDenotation

namespace Example.Tenant.Preparation
open GraphQL GraphQL.Plan GraphQL.Plan.InputCoercion Planning
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def executeKey (adapter : Batching.Actual) (prepared : Prepared operation) (request : Binding.Request)
    (key : Except InputCoercion.Error String) (capacity : Nat) (positive : 0 < capacity) : Batching.Exec Spec.Response :=
  let built := instantiate key prepared.template.val prepared.template.property
  match h : keyError key with
  | none => Batching.execute adapter request ⟨built.resolved, built.clean h⟩ capacity positive
  | some _ => executeResolved request built.resolved

theorem key_execution (adapter : Batching.Actual) (prepared : Prepared operation) (request : Binding.Request)
    (key : Except InputCoercion.Error String) (positive : 0 < capacity) :
    runMachine (Batch.driver adapter) (executeKey adapter prepared request key capacity positive) =
      runMachine (Batch.driver adapter) (executeResolved request (instantiate key prepared.template.val prepared.template.property).resolved) := by
  cases key with
  | ok value =>
    change runMachine _ (Batching.execute adapter request _ capacity positive) = _
    rw [Batching.execute_eq_runtime_any]
    exact (Batch.run_driver adapter _).symm
  | error error => rfl

def PlanDenotes (prepared : Prepared operation) : Prop :=
  ∀ (adapter : Batching.Actual), BindingAgreement Binding.independentBindings adapter →
    ∀ (request : Binding.Request) (key : Except InputCoercion.Error String) (capacity : Nat) (positive : 0 < capacity),
    runMachine (Batch.driver adapter) (executeKey adapter prepared request key capacity positive) =
      InputSurface.Eval request.snapshot request.principal operation key

theorem plan_denotes (prepared : Prepared operation) : PlanDenotes prepared := by
  intro adapter agreement request key capacity positive
  rw [key_execution, resolved_run]
  apply congrArg Spec.envelope
  apply (resolved_transport (Binding.transport request.snapshot)
    (fun principal => (⟨request.snapshot, principal⟩ : Binding.Request)) (meanings request.snapshot) adapter.meanings
    (ExecutionBridge.adapter_transport request.snapshot adapter agreement)
    (instantiate key prepared.template.val prepared.template.property).resolved () request.principal []).trans
  exact (instantiated_denotation prepared.template.val prepared.template.property key () request.principal []).trans
    (parameter_denotation prepared.template.val prepared.template.property key () request.principal [])

inductive KeyMeaning : Option Expr → Environment → Except InputCoercion.Error String → Prop where
  | absent : KeyMeaning none environment (.ok "")
  | value (meaning : Meaning ⟨.id, true⟩ (eval environment expression) (.value value)) :
      KeyMeaning (some expression) environment (.ok value)
  | failure (rejected : Rejected ⟨.id, true⟩ (eval environment expression) error) :
      KeyMeaning (some expression) environment (.error error)

theorem key_complete (meaning : KeyMeaning expression environment key) : idKey expression environment = key := by
  cases meaning with
  | absent => rfl
  | value meaning =>
    simp [idKey, argument, defaulted_none, coerce_complete meaning]
  | failure rejected =>
    have failed := (coerce_rejected _ _ _).mpr rejected
    simp [idKey, argument, defaulted_none, failed]

theorem key_sound (expression : Option Expr) (environment : Environment) :
    KeyMeaning expression environment (idKey expression environment) := by
  cases expression with
  | none => exact .absent
  | some expression =>
    cases result : coerce ⟨.id, true⟩ (eval environment expression) with
    | error code =>
      have identity : idKey (some expression) environment = .error code := by simp [idKey, argument, defaulted_none, result]
      rw [identity]
      exact .failure ((coerce_rejected _ _ _).mp result)
    | ok value =>
      have meaning := coerce_sound _ _ _ result
      obtain ⟨value, equal⟩ := required_value meaning
      cases equal
      have identity : idKey (some expression) environment = .ok value := by
        simp [idKey, argument, defaulted_none, result]
      rw [identity]
      exact .value meaning

inductive RequestError where
  | preparation (error : Error)
  | variable (error : VariableError)
  deriving Repr

def execute (adapter : Batching.Actual) (prepared : Prepared operation) (request : Binding.Request)
    (supplied : Supplied) (capacity : Nat) (positive : 0 < capacity) : Batching.Exec (Except RequestError Spec.Response) :=
  match variables supplied operation.variables with
  | .error error => .done (.error (.variable error))
  | .ok environment => (executeKey adapter prepared request
      (idKey (InputSurface.rootArgument operation.selection) environment) capacity positive).bind
        (fun response => .done (.ok response))

theorem variable_error_no_calls (adapter : Batching.Actual) (prepared : Prepared operation) (request : Binding.Request)
    (supplied : Supplied) (positive : 0 < capacity) (failure : variables supplied operation.variables = .error error) :
    execute adapter prepared request supplied capacity positive = .done (.error (.variable error)) := by
  simp only [execute, failure]

theorem input_meaning_preserved (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (prepared : Prepared operation) (request : Binding.Request) (positive : 0 < capacity)
    (variableMeaning : VariablesMeaning supplied operation.variables environment)
    (argumentMeaning : KeyMeaning (InputSurface.rootArgument operation.selection) environment key) :
    runMachine (Batch.driver adapter) (execute adapter prepared request supplied capacity positive) =
      .ok (InputSurface.Eval request.snapshot request.principal operation key) := by
  simp only [execute, variables_complete variableMeaning, key_complete argumentMeaning, run_bind, runMachine]
  rw [plan_denotes prepared adapter agreement]


/-- Every variable input either has a specified request failure or runs with
independently interpreted variable and argument meanings. -/
theorem execution_cases (adapter : Batching.Actual) (agreement : BindingAgreement Binding.independentBindings adapter)
    (prepared : Prepared operation) (request : Binding.Request) (supplied : Supplied) (positive : 0 < capacity) :
    (∃ error, VariablesRejected supplied operation.variables error ∧
      execute adapter prepared request supplied capacity positive = .done (.error (.variable error))) ∨
    (∃ environment key, VariablesMeaning supplied operation.variables environment ∧
      KeyMeaning (InputSurface.rootArgument operation.selection) environment key ∧
      runMachine (Batch.driver adapter) (execute adapter prepared request supplied capacity positive) =
        .ok (InputSurface.Eval request.snapshot request.principal operation key)) := by
  cases result : variables supplied operation.variables with
  | error error => exact .inl ⟨error, variables_rejected_sound result,
      variable_error_no_calls adapter prepared request supplied positive result⟩
  | ok environment =>
    have variableMeaning := variables_sound _ _ _ result
    have argumentMeaning := key_sound (InputSurface.rootArgument operation.selection) environment
    exact .inr ⟨environment, _, variableMeaning, argumentMeaning,
      input_meaning_preserved adapter agreement prepared request positive variableMeaning argumentMeaning⟩

def executeOperation (adapter : Batching.Actual) (operation : InputSurface.Operation) (request : Binding.Request)
    (supplied : Supplied) (capacity : Nat) (positive : 0 < capacity) : Batching.Exec (Except RequestError Spec.Response) :=
  match prepare operation with
  | .error error => .done (.error (.preparation error))
  | .ok prepared => execute adapter prepared request supplied capacity positive

theorem preparation_error_no_calls (failure : prepare operation = .error error) :
    executeOperation adapter operation request supplied capacity positive = .done (.error (.preparation error)) := by
  simp only [executeOperation, failure]

theorem specified_variable_error_no_calls (failure : VariablesRejected supplied operation.variables error) :
    execute adapter (prepared : Prepared operation) request supplied capacity positive = .done (.error (.variable error)) :=
  variable_error_no_calls adapter prepared request supplied positive (variables_rejected_complete failure)

theorem key_authorized (adapter : Batching.Actual) (prepared : Prepared operation) (request : Binding.Request)
    (key : Except InputCoercion.Error String) (positive : 0 < capacity)
    (permitted : ∀ call, Fault.contracts.Pre call → Fault.contracts.Post call (Batch.driver adapter call)) :
    Spec.AuthorizedResponse request.snapshot request.principal
      (instantiate key prepared.template.val prepared.template.property).selection
      (runMachine (Batch.driver adapter) (executeKey adapter prepared request key capacity positive)) := by
  rw [key_execution]
  exact sat_run _ permitted _ (resolved_authorized request _
    (instantiated_nonempty _ prepared.valid.1.1))

theorem key_conforms (adapter : Batching.Actual) (prepared : Prepared operation) (request : Binding.Request)
    (key : Except InputCoercion.Error String) (positive : 0 < capacity)
    (permitted : ∀ call, Fault.contracts.Pre call → Fault.contracts.Post call (Batch.driver adapter call)) :
    Spec.Conforms (instantiate key prepared.template.val prepared.template.property).selection
      (runMachine (Batch.driver adapter) (executeKey adapter prepared request key capacity positive)) :=
  Fault.authorized_conforms (key_authorized adapter prepared request key positive permitted)

end Example.Tenant.Preparation

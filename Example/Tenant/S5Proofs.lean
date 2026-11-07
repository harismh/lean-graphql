import Example.Tenant.InputText
import Example.Tenant.InputScope
import GraphQL.Plan.Input.NamedBoundary

namespace Example.Tenant.S5Proofs
open GraphQL.Plan GraphQL.Plan.InputCoercion Preparation
set_option maxRecDepth 30000
set_option maxHeartbeats 1600000

def selection : InputSurface.Selection :=
  .field "project" [("id", .variable "id")] (.field "title" [] .nil .nil) .nil

def operation : InputSurface.Operation := { variables := [⟨"id", ⟨.id, true⟩, none⟩], selection := selection }
def defaultOperation : InputSurface.Operation :=
  { variables := [⟨"id", ⟨.id, false⟩, some (.string "shared")⟩], selection := selection }

theorem valid : InputSurface.ValidOperation operation := by decide +kernel
theorem profile : InputSurface.InProfile operation := by decide +kernel
theorem limits : InputSurface.WithinLimits operation := by decide +kernel

def prepared : Prepared operation :=
  ⟨valid, profile, limits, ⟨.object .project "" none
    (.leaf .projectTitle .nil (by decide)) (by intro h; cases h) .nil (by decide), by trivial⟩⟩

def evaluateText (source : String) (supplied : Supplied) : Except String Spec.Response :=
  match prepareText source with
  | .error error => .error (reprStr error)
  | .ok checked => match runMachine (Batch.driver S4bProofs.adapter)
      (execute S4bProofs.adapter checked.2 S4bProofs.request supplied 2 (by decide)) with
    | .error error => .error (reprStr error)
    | .ok response => .ok response

theorem missing_required : variables [] operation.variables = .error ⟨"id", .required⟩ := rfl
theorem integer_id : variables [("id", .int 42)] operation.variables = .ok [("id", some (.string "42"))] := rfl
theorem omitted_default : variables [] defaultOperation.variables = .ok [("id", some (.string "shared"))] := rfl
theorem null_overrides : variables [("id", .null)] defaultOperation.variables = .ok [("id", some .null)] := rfl
theorem null_field_failure : idKey (some (.variable "id")) [("id", some .null)] = .error .required := rfl
theorem int_overflow : coerce ⟨.int, true⟩ (some (.int 2147483648)) = .error .scalar := rfl
theorem absent_is_not_null : coerce ⟨.string, false⟩ none ≠ coerce ⟨.string, false⟩ (some .null) := by intro h; cases h

theorem missing_has_no_calls :
    execute S4bProofs.adapter prepared S4bProofs.request [] 2 (by decide) = .done (.error (.variable ⟨"id", .required⟩)) :=
  variable_error_no_calls _ _ _ _ _ missing_required

theorem shared_meaning :
    runMachine (Batch.driver S4bProofs.adapter)
      (execute S4bProofs.adapter prepared S4bProofs.request [("id", .string "shared")] 2 (by decide)) =
      .ok (InputSurface.Eval S4bProofs.request.snapshot S4bProofs.request.principal operation (.ok "shared")) :=
  input_meaning_preserved _ Generated.application_agreement _ _ _
    (.cons .provided .idString .nil) (.value .idString)

def failed : Except α β → Bool
  | .error _ => true
  | .ok _ => false

def same : Except String Spec.Response → Except String Spec.Response → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

theorem unsupported_type_rejected : ¬ InputSurface.InProfile { operation with declaredTypes := [none] } := by decide +kernel


def defaultPrepared : Prepared defaultOperation :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, prepared.template⟩

theorem argument_error_no_resolver_calls :
    (Batch.runCount (Batch.driver S4bProofs.adapter)
      (execute S4bProofs.adapter defaultPrepared S4bProofs.request [("id", .null)] 2 (by decide))).2 = 0 := by decide +kernel

theorem field_default_on_missing :
    argument ⟨.string, true⟩ (some (.string "fallback")) [] (some (.variable "absent")) = .ok (.value "fallback") := rfl

theorem field_default_preserves_null :
    argument ⟨.string, true⟩ (some (.string "fallback")) [] (some (.literal .null)) = .error .required := rfl

def chain : Nat → InputSurface.Selection
  | 0 => .nil
  | n + 1 => .field "projects" [] (chain n) .nil

theorem depth_boundary : InputSurface.WithinLimits ⟨[], chain 32, []⟩ := by decide +kernel
theorem depth_exceeded : ¬ InputSurface.WithinLimits ⟨[], chain 33, []⟩ := by decide +kernel
theorem variable_boundary : InputSurface.WithinLimits ⟨List.replicate 32 ⟨"id", ⟨.id, true⟩, none⟩, .nil, []⟩ := by decide +kernel
theorem variable_exceeded : ¬ InputSurface.WithinLimits ⟨List.replicate 33 ⟨"id", ⟨.id, true⟩, none⟩, .nil, []⟩ := by decide +kernel

/-- Parser tests supplement the decoded-AST theorem; they do not prove parsing fidelity. -/
def nativeTests : IO Unit := do
  let query := "query($id: ID!) { project(id: $id) { title } }"
  let success := evaluateText query [("id", .string "shared")]
  unless same success (.ok (InputSurface.Eval S4bProofs.request.snapshot S4bProofs.request.principal operation (.ok "shared"))) do
    throw (IO.userError "S5 variable execution mismatch")
  unless failed (evaluateText query []) do throw (IO.userError "S5 missing variable accepted")
  unless failed (evaluateText query [("id", .boolean true)]) do throw (IO.userError "S5 wrong variable scalar accepted")
  let defaultQuery := "query($id: ID = \"shared\") { project(id: $id) { title } }"
  unless same (evaluateText defaultQuery []) success do throw (IO.userError "S5 default mismatch")
  match evaluateText defaultQuery [("id", .null)] with
  | .error _ => throw (IO.userError "S5 null should be a field error")
  | .ok response => unless response.errors.length == 1 do throw (IO.userError "S5 missing field error")
  for source in ["query($id: ID) { project(id: $id) { title } }",
      "query($id: String!) { project(id: $id) { title } }",
      "query($id: ID!, $id: ID!) { project(id: $id) { title } }",
      "query($unused: ID) { projects { title } }", "{ project(id: $missing) { title } }",
      "{ unknown }", "{ projects { other: title } }", "{ projects @skip(if: true) { title } }",
      "{ project { title } }", "{ project(id: {}) { title } }",
      "{ project(id: []) { title } }", "{ project(id: SOME) { title } }"] do
    unless failed (prepareText source) do throw (IO.userError s!"S5 invalid operation accepted: {source}")
  let batched := evaluateText "{ projects { tasks { project { title } } } }" []
  unless same batched (.ok (Runtime.run S4bProofs.adapter S4bProofs.request S4bProofs.selected)) do
    throw (IO.userError "S5 parsed batch response mismatch")
  unless (InputCoercion.NamedExample.coerceNamed [] [("right", .literal (.string "R")), ("left", .literal (.string "L"))]).toOption == some ("L", "R") do
    throw (IO.userError "S5 named coercion mismatch")
  unless (evaluateText query [("id", .string "missing")]).toOption != success.toOption do
    throw (IO.userError "S5 template did not depend on variable value")
  unless failed (prepareText (String.ofList (List.replicate 32769 ' '))) do
    throw (IO.userError "S5 text limit not enforced")
  unless (jsonVariables (.mkObj [("id", .null)])).toOption == some [("id", .null)] do
    throw (IO.userError "S5 JSON null lost")
  unless (InputCoercion.NamedBoundary.execute InputCoercion.NamedBoundary.adapter []
      [("right", .literal (.string "R")), ("left", .literal (.string "L"))]).toOption == some "L:R" do
    throw (IO.userError "S5 named binding graph execution mismatch")
  IO.println "S5: text preparation, variables, defaults, field errors, batching, and named inputs passed."

end Example.Tenant.S5Proofs

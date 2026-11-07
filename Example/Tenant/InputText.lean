import Example.Tenant.PreparedExecution
import GraphQL.Syntax

namespace Example.Tenant.Preparation
open GraphQL.Plan GraphQL.Plan.InputCoercion

/-- Decoding fidelity is outside the theorem. Unsupported forms remain explicit
and cannot bypass the subsequent independent profile/type checks. -/
def decodeRaw : GraphQL.InputValue → Raw
  | .null => .null
  | .string value => .string value
  | .int value => .int value
  | .boolean value => .boolean value
  | _ => .unsupported

def decodeExpr : GraphQL.InputValue → Expr
  | .variable name => .variable name
  | value => .literal (decodeRaw value)

def decodeType : GraphQL.TypeRef → Option ScalarType
  | .named "ID" required => some ⟨.id, required⟩
  | .named "String" required => some ⟨.string, required⟩
  | .named "Int" required => some ⟨.int, required⟩
  | .named "Boolean" required => some ⟨.boolean, required⟩
  | _ => none

def decodeSelections : List GraphQL.Selection → InputSurface.Selection
  | [] => .nil
  | .field name key arguments directives children _ :: rest =>
    if key = name ∧ directives.isEmpty then
      .field name (arguments.map (fun (name, value) => (name, decodeExpr value)))
        (decodeSelections children) (decodeSelections rest)
    else .excluded
  | .fragment .. :: _ => .excluded
termination_by selections => sizeOf selections

def decodeOperation (operation : GraphQL.Operation) : InputSurface.Operation :=
  ⟨operation.variables.map (fun declaration =>
    ⟨declaration.name, (decodeType declaration.type).getD ⟨.string, false⟩, declaration.defaultValue.map decodeRaw⟩),
    decodeSelections operation.selections, operation.variables.map (fun declaration => decodeType declaration.type)⟩

inductive TextError where
  | parse (message : String)
  | tooLarge
  | preparation (error : Error)
  deriving Repr

abbrev TextPrepared := (operation : InputSurface.Operation) × Prepared operation

def prepareText (source : String) : Except TextError TextPrepared :=
  if source.length > 32768 then .error .tooLarge else
  match GraphQL.parseOperation source with
  | .error message => .error (.parse message)
  | .ok decoded =>
    let operation := decodeOperation decoded
    match prepare operation with
    | .error error => .error (.preparation error)
    | .ok prepared => .ok ⟨operation, prepared⟩

theorem text_preparation_sound (prepared : TextPrepared) :
    InputSurface.ValidOperation prepared.1 ∧ InputSurface.InProfile prepared.1 ∧ InputSurface.WithinLimits prepared.1 :=
  prepare_sound prepared.2

/-- JSON values are decoded without silently stringifying wrong scalar types. -/
def jsonRaw : Lean.Json → Raw
  | .null => .null
  | .str value => .string value
  | .bool value => .boolean value
  | .num number => match (Lean.Json.num number).getInt? with | .ok value => .int value | .error _ => .unsupported
  | _ => .unsupported

def jsonVariables (json : Lean.Json) : Except String Supplied :=
  match json.getObj? with
  | .error message => .error message
  | .ok object => .ok (object.toList.map (fun (name, value) => (name, jsonRaw value)))

end Example.Tenant.Preparation

import GraphQL.Value

namespace GraphQL

abbrev Inputs := List (String × InputValue)

def distinctKeys (values : List (String × α)) : Bool := decide (unique (values.map Prod.fst))

/-- Executable input coercion. Its complete soundness theorem is outside this first slice. -/
def coerceInput (s : Schema) (fromJson : Bool) : Nat → TypeRef → InputValue → Except String InputValue
  | 0, _, _ => .error "input depth limit exceeded"
  | fuel + 1, t, value => do
    if let .null := value then
      if t.isRequired then throw "null supplied for a non-null input" else return .null
    match t with
    | .list item _ =>
      let items := match value with | .list xs => xs | v => [v]
      return .list (← items.mapM (coerceInput s fromJson fuel item))
    | .named n _ =>
      if n == "String" then return .string (← inputString value)
      if n == "ID" then return .string (← inputID value)
      if n == "Int" then return .int (← inputInt value).toInt
      if n == "Boolean" then return .boolean (← inputBool value)
      match s.find? n with
      | none => throw s!"unknown input type '{n}'"
      | some definition =>
        if definition.kind == .scalar then return .string (← inputString value)
        if definition.kind == .enumType then
          let member ← match value with
            | .enumValue n => pure n
            | .string n => if fromJson then pure n else throw "enum literals must be unquoted"
            | _ => throw s!"expected enum {n}"
          unless definition.members.contains member do throw s!"invalid {n} member '{member}'"
          return .enumValue member
        unless definition.kind == .input do throw s!"'{n}' is not an input type"
        let fields ← match value with | .object fs => pure fs | _ => throw s!"expected input object {n}"
        unless distinctKeys fields do throw "duplicate input field"
        for (key, _) in fields do
          unless definition.fields.any (·.name == key) do throw s!"unknown input field {n}.{key}"
        let coerced ← definition.fields.foldlM (init := []) fun acc field => do
          match fields.lookup field.name with
          | none =>
            if field.type.isRequired then throw s!"missing input field {n}.{field.name}"
            else return acc
          | some v => return acc ++ [(field.name, ← coerceInput s fromJson fuel field.type v)]
        return .object coerced

def resolveVariables (variables : Inputs) : Nat → InputValue → Except String (Option InputValue)
  | 0, _ => .error "input depth limit exceeded"
  | _ + 1, .variable n => return variables.lookup n
  | fuel + 1, .list xs => do
    return some (.list (← xs.mapM fun v => return (← resolveVariables variables fuel v).getD .null))
  | fuel + 1, .object xs => do
    let fields ← xs.foldlM (init := []) fun acc (k, v) => do
      match ← resolveVariables variables fuel v with
      | none => return acc
      | some value => return acc ++ [(k, value)]
    return some (.object fields)
  | _ + 1, v => return some v

def variableAllowed : TypeRef → TypeRef → Bool → Bool
  | .named a ar, .named b br, hasDefault => a == b && (!br || ar || hasDefault)
  | .list a ar, .list b br, hasDefault => (!br || ar || hasDefault) && variableAllowed a b false
  | _, _, _ => false

def validateValue (s : Schema) (variables : List VariableDef) : Nat → TypeRef → InputValue → Except String Unit
  | 0, _, _ => throw "input depth limit exceeded"
  | fuel + 1, t, value => do
    if let .variable n := value then
      let some v := variables.find? (·.name == n) | throw s!"undefined variable ${n}"
      let hasDefault := v.defaultValue.any (· != .null)
      unless variableAllowed v.type t hasDefault do throw s!"incompatible type for variable ${n}"
      return ()
    if let .null := value then
      if t.isRequired then throw "null literal for a non-null input" else return ()
    match t with
    | .list item _ =>
      let items := match value with | .list xs => xs | v => [v]
      items.forM (validateValue s variables fuel item)
    | .named n _ =>
      if let some definition := s.find? n then
        if definition.kind == .input then
          let .object fields := value | throw s!"expected input object {n}"
          unless distinctKeys fields do throw "duplicate input field"
          for (key, v) in fields do
            let some f := definition.fields.find? (·.name == key) | throw s!"unknown input field {n}.{key}"
            validateValue s variables fuel f.type v
          for field in definition.fields do
            if field.type.isRequired && !(fields.any (·.1 == field.name)) then
              throw s!"missing input field {n}.{field.name}"
          return ()
      let _ ← coerceInput s false (fuel + 1) t value

structure CollectedField where
  name : String
  key : String
  arguments : Inputs
  children : List Selection
  offset : Nat
  deriving Repr, Inhabited

def directiveEnabled (variables : Inputs) (d : Directive) : Except String Bool := do
  let some value ← resolveVariables variables 16 d.condition | throw "missing directive condition"
  let flag ← inputBool value
  return if d.name == "skip" then !flag else flag

def collectFields (s : Schema) (variables : Inputs) (actual : String) :
    Nat → String → List Selection → Except String (List CollectedField)
  | 0, _, _ => throw "selection budget exhausted"
  | fuel + 1, scope, selections => selections.foldlM (init := []) fun acc selection => do
    match selection with
    | .fragment target children _ =>
      if s.possibleType target actual then
        return acc ++ (← collectFields s variables actual fuel target children)
      else return acc
    | .field name key args ds children offset =>
      unless name == "__typename" || (s.field? scope name).isSome do
        throw s!"unknown field {scope}.{name} at character {offset}"
      let enabled ← ds.mapM (directiveEnabled variables)
      if enabled.contains false then return acc
      return acc ++ [⟨name, key, args, children, offset⟩]

def mergeField (fields : List CollectedField) (incoming : CollectedField) : Except String (List CollectedField) :=
  match fields with
  | [] => return [incoming]
  | f :: rest =>
    if f.key == incoming.key then
      if f.name == incoming.name && f.arguments == incoming.arguments then
        return { f with children := f.children ++ incoming.children } :: rest
      else throw s!"conflicting selections for response key '{f.key}'"
    else return f :: (← mergeField rest incoming)

def mergedFields (s : Schema) (vars : Inputs) (actual scope : String)
    (sels : List Selection) : Except String (List CollectedField) := do
  let fields ← collectFields s vars actual 256 scope sels
  fields.foldlM mergeField []

def fieldDefinition (s : Schema) (owner name : String) : Except String Field :=
  if name == "__typename" then .ok ⟨name, .named "String" true, []⟩
  else match s.field? owner name with
    | some f => .ok f
    | none => .error s!"unknown field {owner}.{name}"

/-- All structural and pairwise checks share one request-level work allowance. -/
private abbrev Validation := StateT Nat (Except String)

private def spend : Validation Unit := do
  match ← get with
  | 0 => throw "validation work exceeds 100000 units"
  | n + 1 => set n

private def validateTree (s : Schema) (variables : List VariableDef) :
    Nat → String → List Selection → Validation Unit
  | 0, _, _ => throw "selection nesting exceeds 64 levels"
  | fuel + 1, owner, sels => do
    unless s.compositeName owner do throw s!"'{owner}' is not a composite output type"
    for selection in sels do
      spend
      match selection with
      | .fragment target children _ =>
        unless s.compositeName target && (owner == target || s.types.any
            (fun t => s.possibleType owner t.name && s.possibleType target t.name)) do
          throw s!"fragment on '{target}' cannot apply to '{owner}'"
        validateTree s variables fuel target children
      | .field name _ arguments ds children offset =>
        let definition ← fieldDefinition s owner name
        unless decide (unique (ds.map (·.name))) do throw "duplicate directive"
        for d in ds do
          -- Deliberate prototype restriction: no nullable variable/default exception here.
          if let .variable n := d.condition then
            let some v := variables.find? (·.name == n) | throw s!"undefined variable ${n}"
            unless v.type == .named "Boolean" true do
              throw s!"directive variable ${n} must have type Boolean!"
          validateValue s variables 128 (.named "Boolean" true) d.condition
        unless distinctKeys arguments do throw "duplicate argument"
        for (name, value) in arguments do
          let some arg := definition.arguments.find? (·.name == name) | throw s!"unknown argument '{name}' at character {offset}"
          validateValue s variables 128 arg.type value
        for arg in definition.arguments do
          if arg.type.isRequired && !(arguments.any (·.1 == arg.name)) then
            throw s!"missing required argument '{arg.name}' at character {offset}"
        if s.compositeName definition.type.base then
          if children.isEmpty then throw s!"field '{name}' requires a selection"
          validateTree s variables fuel definition.type.base children
        else unless children.isEmpty do throw s!"scalar field '{name}' cannot have a selection"

private structure ScopedField where
  scope : String
  definition : Field
  selected : CollectedField
  deriving Inhabited

/-- Flatten only fragments, keeping each field's declared scope for merge checks. -/
private def scopedFields (s : Schema) : Nat → String → List Selection → Validation (List ScopedField)
  | 0, _, _ => throw "fragment nesting exceeds limit"
  | fuel + 1, scope, sels => do
    sels.foldlM (init := []) fun acc selection => do
      spend
      match selection with
      | .fragment target children _ => return acc ++ (← scopedFields s fuel target children)
      | .field name key args _ children offset =>
        return acc ++ [⟨scope, ← fieldDefinition s scope name, ⟨name, key, args, children, offset⟩⟩]

private def sameTypeShape (s : Schema) : TypeRef → TypeRef → Bool
  | .list a ar, .list b br => ar == br && sameTypeShape s a b
  | .named a ar, .named b br =>
    ar == br && (if s.compositeName a then s.compositeName b else a == b)
  | _, _ => false

/-- SameResponseShape also applies to mutually exclusive concrete object branches. -/
private def compareFields (s : Schema) : Nat → Bool → ScopedField → ScopedField → Validation Unit
  | 0, _, _, _ => throw "merge nesting exceeds limit"
  | fuel + 1, exclusive, a, b => do
    spend
    if a.selected.key != b.selected.key then return ()
    unless sameTypeShape s a.definition.type b.definition.type do
      throw s!"incompatible response shape for key '{a.selected.key}'"
    let exclusive := exclusive || (s.objectName a.scope && s.objectName b.scope && a.scope != b.scope)
    unless exclusive || (a.selected.name == b.selected.name && a.selected.arguments == b.selected.arguments) do
      throw s!"conflicting selections for response key '{a.selected.key}'"
    if s.compositeName a.definition.type.base then
      let left ← scopedFields s 64 a.definition.type.base a.selected.children
      let right ← scopedFields s 64 b.definition.type.base b.selected.children
      for x in left do
        for y in right do compareFields s fuel exclusive x y

private def validateMerges (s : Schema) : Nat → String → List Selection → Validation Unit
  | 0, _, _ => throw "merge nesting exceeds limit"
  | fuel + 1, scope, sels => do
    let fields ← scopedFields s 64 scope sels
    for i in [:fields.length] do
      let field := fields[i]!
      for other in fields.drop (i + 1) do compareFields s fuel false field other
      if s.compositeName field.definition.type.base then
        validateMerges s fuel field.definition.type.base field.selected.children

def validateSelections (s : Schema) (variables : List VariableDef) (owner : String)
    (sels : List Selection) : Except String Unit := do
  let checks : Validation Unit := do
    validateTree s variables 64 owner sels
    validateMerges s 64 owner sels
  checks.run' 100000

def inputVariables : Nat → InputValue → List String
  | 0, _ => []
  | _ + 1, .variable n => [n]
  | fuel + 1, .list xs => xs.flatMap (inputVariables fuel)
  | fuel + 1, .object xs => xs.flatMap (inputVariables fuel ·.2)
  | _ + 1, _ => []

def selectionVariables : Nat → Selection → List String
  | 0, _ => []
  | fuel + 1, .field _ _ args ds children _ =>
    args.flatMap (inputVariables 128 ·.2) ++ ds.flatMap (inputVariables 128 ·.condition) ++ children.flatMap (selectionVariables fuel)
  | fuel + 1, .fragment _ children _ => children.flatMap (selectionVariables fuel)

/-- Runtime typestate. Validation soundness for this prototype validator is not yet proved. -/
structure Plan where
  private mk ::
  schema : CheckedSchema
  operation : Operation

private def validateOperation (schema : CheckedSchema) (operation : Operation) : Except String Plan := do
  unless decide (unique (operation.variables.map (·.name))) do throw "duplicate variable definition"
  let used := operation.selections.flatMap (selectionVariables 256)
  for varDef in operation.variables do
    unless used.contains varDef.name do throw s!"unused variable ${varDef.name}"
    unless schema.data.inputName varDef.type.base do throw "variable type must be an input type"
    if let some value := varDef.defaultValue then
      let _ ← coerceInput schema.data false 128 varDef.type value
  validateSelections schema.data operation.variables schema.data.query operation.selections
  return ⟨schema, operation⟩

inductive PrepareError where
  | parse (message : String)
  | validation (message : String)
  deriving Repr

def PrepareError.message : PrepareError → String
  | .parse m | .validation m => m

/-- Parse once and preserve the diagnostic's phase for transport status selection. -/
def prepareDetailed (schema : CheckedSchema) (source : String) : Except PrepareError Plan := do
  let operation ← (parseOperation source).mapError PrepareError.parse
  (validateOperation schema operation).mapError PrepareError.validation

def prepare (schema : CheckedSchema) (source : String) : Except String Plan :=
  (prepareDetailed schema source).mapError PrepareError.message

def coerceVariables (plan : Plan) (provided : Inputs) : Except String Inputs := do
  unless distinctKeys provided do throw "duplicate variable key"
  plan.operation.variables.foldlM (init := []) fun acc v => do
    match provided.lookup v.name with
    | some value => return acc ++ [(v.name, ← coerceInput plan.schema.data true 128 v.type value)]
    | none => match v.defaultValue with
      | some value => return acc ++ [(v.name, ← coerceInput plan.schema.data false 128 v.type value)]
      | none => if v.type.isRequired then throw s!"missing variable ${v.name}" else return acc

def coerceArguments (schema : Schema) (field : Field) (arguments variables : Inputs) : Except String Inputs :=
  field.arguments.foldlM (init := []) fun acc arg => do
    let value ← match arguments.lookup arg.name with
      | none => pure none
      | some v => resolveVariables variables 128 v
    match value with
    | none => if arg.type.isRequired then throw s!"missing argument '{arg.name}'" else return acc
    | some v => return acc ++ [(arg.name, ← coerceInput schema false 128 arg.type v)]

end GraphQL

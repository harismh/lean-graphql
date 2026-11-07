import GraphQL.Validation

namespace GraphQL

private def failure (required : Bool) (path : List PathSegment) (message : String) : Completion :=
  nullableBoundary required (.bubble [⟨message, path⟩])

mutual
  def executeObject (s : Schema) (variables : Inputs) : Nat → String → Nat → List Selection → List PathSegment → Execution Completion
    | 0, _, _, _, path => pure (failure true path "execution depth limit exceeded")
    | fuel + 1, owner, parent, selections, path => do
      match mergedFields s variables owner owner selections with
      | .error e => return failure true path e
      | .ok fields =>
        let results ← fields.mapM fun selected => do
          let fieldPath := path ++ [.field selected.key]
          match fieldDefinition s owner selected.name with
          | .error e => return failure true fieldPath e
          | .ok field =>
            match coerceArguments s field selected.arguments variables with
            | .error e => return failure field.type.isRequired fieldPath e
            | .ok arguments =>
              if field.name == "__typename" then return .value (.string owner) []
              let outcome ← Machine.pending ⟨owner, parent, field, arguments, fieldPath⟩ Machine.done
              match outcome with
              | .error message => return failure field.type.isRequired fieldPath message
              | .ok raw => completeValue s variables fuel field.type raw selected.children fieldPath
        let (values, errors) := collectItems results
        match values with
        | none => return .bubble errors
        | some values => return .value (.object ((fields.map (·.key)).zip values)) errors

  def completeValue (s : Schema) (variables : Inputs) : Nat → TypeRef → RawValue → List Selection → List PathSegment → Execution Completion
    | 0, t, _, _, path => pure (failure t.isRequired path "completion depth limit exceeded")
    | fuel + 1, t, raw, children, path => do
      if let .null := raw then
        if t.isRequired then return failure true path "non-null field resolved to null"
        else return .value .null []
      match t with
      | .list item required =>
        let .list values := raw | return failure required path "resolver returned a non-list value"
        let results ← values.zipIdx |>.mapM fun (value, index) =>
          completeValue s variables fuel item value children (path ++ [.index index])
        return completeList required results
      | .named name required =>
        if s.compositeName name then
          let .object actual key := raw | return failure required path "resolver returned a non-object value"
          unless s.possibleType name actual do return failure required path "invalid abstract type member"
          return nullableBoundary required (← executeObject s variables fuel actual key children path)
        let value : Except String ResponseValue :=
          if name == "String" || name == "ID" then
            match raw with | .string v => .ok (.string v) | _ => .error "invalid string result"
          else if name == "Int" then
            match raw with
            | .int v => if -2147483648 ≤ v && v ≤ 2147483647 then .ok (.int v) else .error "Int result out of range"
            | _ => .error "invalid Int result"
          else if name == "Boolean" then
            match raw with | .boolean v => .ok (.boolean v) | _ => .error "invalid Boolean result"
          else match s.find? name with
            | some t =>
              if t.kind == .enumType then
                match raw with
                | .enumValue v => if t.members.contains v then .ok (.string v) else .error "invalid enum result"
                | _ => .error "invalid enum result"
              else if t.kind == .scalar then
                match raw with | .string v => .ok (.string v) | _ => .error "invalid custom scalar result"
              else .error "unsupported output type"
            | none => .error "unknown output type"
        match value with
        | .ok v => return .value v []
        | .error e => return failure required path e
end

def execute (plan : Plan) (variables : Inputs := []) : Except String (Execution Completion) := do
  let variables ← coerceVariables plan variables
  return executeObject plan.schema.data variables 256 plan.schema.data.query 0 plan.operation.selections []

/-- Small effect driver. Safety of effect implementations and scheduling is not proved. -/
def drive [Monad m] (resolve : Call → m (Except String RawValue)) : Execution α → m α
  | .done value => pure value
  | .pending call resume => do
    let result ← resolve call
    drive resolve (resume result)

end GraphQL

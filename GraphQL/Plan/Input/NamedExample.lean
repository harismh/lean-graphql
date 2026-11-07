import GraphQL.Plan.Input.Variables
import GraphQL.Plan.Interpreter

namespace GraphQL.Plan.InputCoercion.NamedExample

/-- The independent schema fixes both names, despite equal host types. -/
def layout : List GraphQL.Argument := [⟨"left", .named "String" true⟩, ⟨"right", .named "String" true⟩]
def left : NamedArgument layout "left" := ⟨⟨0, by decide⟩, rfl⟩
def right : NamedArgument layout "right" := ⟨⟨1, by decide⟩, rfl⟩
def specification (a b : String) := a ++ ":" ++ b
def resolver (record : ArgumentRecord layout) : String := specification (left.read record) (right.read record)

def schema : Schema := ⟨1, fun _ => [⟨"join", argumentCode layout, .string⟩]⟩
def field : FieldId schema ⟨0, by decide⟩ := ⟨⟨0, by decide⟩⟩
def models : Fin 1 → Type := fun _ => Unit

def meanings : Meanings schema models Unit Empty := fun f _ _ args =>
  match f with
  | ⟨⟨0, _⟩⟩ => .ok (resolver (packArguments layout args))

def program (args : String × String) : Machine (Call schema models Unit) (Answer Empty) (Outcome Empty String) :=
  .pending (.one field () () args) .done

def coerceNamed (environment : Environment) (arguments : List (String × Expr)) : Except Error (String × String) := do
  let first ← argument ⟨.string, true⟩ none environment (lookup layout[left.index].name arguments)
  let second ← argument ⟨.string, true⟩ none environment (lookup layout[right.index].name arguments)
  match first, second with
  | .value a, .value b => .ok (a, b)
  | _, _ => .error .required

def execute (environment : Environment) (arguments : List (String × Expr)) :
    Machine (Call schema models Unit) (Answer Empty) (Outcome Empty String) :=
  match coerceNamed environment arguments with
  | .error _ => .done (.error (.framework .argument))
  | .ok args => program args

theorem named_resolver_contract (a b : String) :
    resolver (packArguments layout (a, b)) = specification a b := rfl

theorem execution_contract (success : coerceNamed environment arguments = .ok (a, b)) :
    runMachine (denoteCall meanings) (execute environment arguments) = .ok (specification a b) := by
  simp only [execute, success]
  rfl

theorem named_coercion_complete
    (first : Meaning ⟨.string, true⟩ ((lookup "left" arguments).bind (eval environment)) (.value a))
    (second : Meaning ⟨.string, true⟩ ((lookup "right" arguments).bind (eval environment)) (.value b)) :
    coerceNamed environment arguments = .ok (a, b) := by
  simp [coerceNamed, layout, left, right, argument, defaulted_none, coerce_complete first, coerce_complete second]
  rfl

theorem named_field_meaning (first : Meaning ⟨.string, true⟩ ((lookup "left" arguments).bind (eval environment)) (.value a))
    (second : Meaning ⟨.string, true⟩ ((lookup "right" arguments).bind (eval environment)) (.value b)) :
    runMachine (denoteCall meanings) (execute environment arguments) = .ok (specification a b) :=
  execution_contract (named_coercion_complete first second)

theorem order_independent :
    runMachine (denoteCall meanings) (execute [] [("right", .literal (.string "R")), ("left", .literal (.string "L"))]) = .ok "L:R" := rfl

def swappedMeanings : Meanings schema models Unit Empty := fun f _ _ args =>
  match f with
  | ⟨⟨0, _⟩⟩ => .ok (resolver (packArguments layout (args.2, args.1)))

theorem swapped_execution_detected :
    runMachine (denoteCall swappedMeanings) (program ("L", "R")) ≠ .ok (specification "L" "R") := by
  change (Except.ok "R:L" : Outcome Empty String) ≠ .ok "L:R"
  intro equal
  have impossible := Except.ok.inj equal
  exact (by decide : "R:L" ≠ "L:R") impossible

end GraphQL.Plan.InputCoercion.NamedExample

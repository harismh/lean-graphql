import GraphQL.Plan.Input.NamedBindings
import GraphQL.Plan.Input.NamedExample

namespace GraphQL.Plan.InputCoercion.NamedBoundary
open NamedExample (layout left right specification resolver coerceNamed)

abbrev ast : GraphQL.Schema := ⟨[⟨"Query", .object, [⟨"join", .named "String" true, layout⟩], [], []⟩], "Query"⟩
def indexed : IndexedSchema ast := ⟨fun _ => [⟨"join", .pair .string .string, .string⟩], 0, fun _ _ => layout⟩
abbrev checked : CheckedIndexed ast := ⟨indexed, by decide +kernel, by decide +kernel⟩
abbrev field := checked.field 0 ⟨0, by decide⟩
def models : Fin 1 → Type := fun _ => Unit

/-- Independent semantic record, defined by named schema coordinates rather than
by the library's positional packer. -/
def inputRecord (a b : String) : ArgumentRecord layout
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨n + 2, bound⟩ => False.elim (by simp [layout] at bound; omega)

def target : BindingsByField checked models Unit Empty := fun owner coordinate =>
  match owner, coordinate with
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨fun _ _ args => .ok (resolver (inputRecord args.1 args.2)), none⟩

def bindings : BindingsByField checked models Unit Empty := fun owner coordinate =>
  match owner, coordinate with
  | ⟨0, _⟩, ⟨0, _⟩ => namedFieldBinding checked 0 ⟨0, by decide⟩ (fun _ _ record => .ok (resolver record))

def adapter : Adapter checked.indexed.schema models Unit Empty := adaptBindings bindings

theorem binding_agreement : BindingAgreement target adapter := by
  intro owner coordinate
  rcases owner with ⟨n, bound⟩
  have zero : n = 0 := by simp [ast] at bound; omega
  subst n
  rcases coordinate with ⟨n, bound⟩
  have zero : n = 0 := by simp [ast] at bound; omega
  subst n
  rfl

def graph : Graph checked.indexed.schema models Unit Empty [String × String, Unit, Unit]
    [Outcome Empty String, String × String, Unit, Unit] :=
  .snoc .nil (.call field (.there .here) (.there (.there .here)) .here)

def execute (usingAdapter : Adapter checked.indexed.schema models Unit Empty)
    (environment : Environment) (arguments : List (String × Expr)) : Outcome Empty String :=
  match coerceNamed environment arguments with
  | .error _ => .error (.framework .argument)
  | .ok args => (runMachine (answerBinding usingAdapter) (interpretGraph graph (args, (), (), ()))).1

theorem execution_meaning (agreement : BindingAgreement target usingAdapter)
    (first : Meaning ⟨.string, true⟩ ((lookup "left" arguments).bind (eval environment)) (.value a))
    (second : Meaning ⟨.string, true⟩ ((lookup "right" arguments).bind (eval environment)) (.value b)) :
    execute usingAdapter environment arguments = .ok (specification a b) := by
  rw [execute, NamedExample.named_coercion_complete first second]
  change (usingAdapter field).single () () (a, b) = _
  rw [agreement 0 ⟨0, by decide⟩]
  rfl

/-- A type-correct adapter mutation swaps the library's pack order. -/
def swappedBindings : BindingsByField checked models Unit Empty := fun owner coordinate =>
  match owner, coordinate with
  | ⟨0, _⟩, ⟨0, _⟩ => ⟨fun _ _ args => .ok (resolver (packArguments layout (args.2, args.1))), none⟩
def swappedAdapter : Adapter checked.indexed.schema models Unit Empty := adaptBindings swappedBindings

theorem swapped_binding_rejected : ¬ BindingAgreement target swappedAdapter := by
  intro agreement
  have wrong := congrArg (fun binding => binding.single () () ("L", "R")) (agreement 0 ⟨0, by decide⟩)
  have unequal : ("R:L" : String) ≠ "L:R" := by decide
  exact unequal (Except.ok.inj wrong)

/-- Coercion agreement is stated using the independent name-indexed meanings. -/
def CoercionAgreement (coercer : Environment → List (String × Expr) → Except Error (String × String)) : Prop :=
  ∀ environment arguments a b,
    Meaning ⟨.string, true⟩ ((lookup "left" arguments).bind (eval environment)) (.value a) →
    Meaning ⟨.string, true⟩ ((lookup "right" arguments).bind (eval environment)) (.value b) →
    coercer environment arguments = .ok (a, b)

theorem coercion_agreement : CoercionAgreement coerceNamed := by
  intro environment arguments a b first second
  exact NamedExample.named_coercion_complete first second

def swappedCoercion (environment : Environment) (arguments : List (String × Expr)) : Except Error (String × String) := do
  let first ← argument ⟨.string, true⟩ none environment (lookup "right" arguments)
  let second ← argument ⟨.string, true⟩ none environment (lookup "left" arguments)
  match first, second with
  | .value a, .value b => .ok (a, b)
  | _, _ => .error .required

theorem swapped_coercion_rejected : ¬ CoercionAgreement swappedCoercion := by
  intro agreement
  have wrong := agreement [] [("left", .literal (.string "L")), ("right", .literal (.string "R"))] "L" "R" .string .string
  have unequal : ("R" : String) ≠ "L" := by decide
  exact unequal (congrArg Prod.fst (Except.ok.inj wrong))

theorem graph_executes_named_arguments :
    execute adapter [] [("right", .literal (.string "R")), ("left", .literal (.string "L"))] = .ok "L:R" :=
  execution_meaning (environment := []) (arguments := [("right", .literal (.string "R")), ("left", .literal (.string "L"))]) (a := "L") (b := "R") binding_agreement .string .string

end GraphQL.Plan.InputCoercion.NamedBoundary

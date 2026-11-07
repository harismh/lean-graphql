import GraphQL.Plan.Input.Coercion

namespace GraphQL.Plan.InputCoercion

structure Variable where
  name : String
  type : ScalarType
  fallback : Option Raw := none
  deriving DecidableEq, Repr

inductive Expr where
  | literal (value : Raw)
  | variable (name : String)
  deriving DecidableEq, Repr

abbrev Supplied := List (String × Raw)
abbrev Environment := List (String × Option Raw)

def lookup {α : Type} (name : String) : List (String × α) → Option α
  | [] => none
  | (key, value) :: rest => if key = name then some value else lookup name rest

def eval (environment : Environment) : Expr → Option Raw
  | .literal value => some value
  | .variable name => (lookup name environment).join

structure VariableError where
  name : String
  code : Error
  deriving DecidableEq, Repr

def variables (supplied : Supplied) : List Variable → Except VariableError Environment
  | [] => .ok []
  | declaration :: rest =>
    match coerce declaration.type (defaulted declaration.fallback (lookup declaration.name supplied)) with
    | .error code => .error ⟨declaration.name, code⟩
    | .ok value => match variables supplied rest with
      | .error error => .error error
      | .ok tail => .ok ((declaration.name, encode declaration.type.scalar value) :: tail)

/-- Ordered relational interpretation, independent of the coercer's control flow. -/
inductive VariablesMeaning (supplied : Supplied) : List Variable → Environment → Prop where
  | nil : VariablesMeaning supplied [] []
  | cons {declaration : Variable} {typed : Input declaration.type.scalar.denote} (defaulting : DefaultMeaning declaration.fallback (lookup declaration.name supplied) effective)
      (value : Meaning declaration.type effective typed)
      (tail : VariablesMeaning supplied rest environment) :
      VariablesMeaning supplied (declaration :: rest)
        ((declaration.name, encode declaration.type.scalar typed) :: environment)

theorem variables_complete (meaning : VariablesMeaning supplied declarations environment) :
    variables supplied declarations = .ok environment := by
  induction meaning with
  | nil => rfl
  | cons defaulting value tail ih =>
    simp [variables, Except.mapError, Except.bind, Except.map, defaulted_complete defaulting, coerce_complete value, ih]

theorem variables_sound (declarations : List Variable) (supplied : Supplied) (environment : Environment)
    (success : variables supplied declarations = .ok environment) : VariablesMeaning supplied declarations environment := by
  induction declarations generalizing environment with
  | nil => cases success; exact .nil
  | cons declaration rest ih =>
    cases first : coerce declaration.type (defaulted declaration.fallback (lookup declaration.name supplied)) with
    | error code => simp [variables, Except.mapError, Except.bind, Except.map, first] at success
    | ok value =>
      cases remaining : variables supplied rest with
      | error error => simp [variables, Except.mapError, Except.bind, Except.map, first, remaining] at success
      | ok tail =>
        simp [variables, Except.mapError, Except.bind, Except.map, first, remaining] at success
        subst environment
        exact .cons (defaulted_sound _ _) (coerce_sound _ _ _ first) (ih tail remaining)

/-- The first failing declaration, with successful coercions before it. -/
inductive VariablesRejected (supplied : Supplied) : List Variable → VariableError → Prop where
  | head {declaration : Variable}
      (defaults : DefaultMeaning declaration.fallback (lookup declaration.name supplied) effective)
      (failure : Rejected declaration.type effective code) :
      VariablesRejected supplied (declaration :: rest) ⟨declaration.name, code⟩
  | tail {declaration : Variable} {typed : Input declaration.type.scalar.denote}
      (defaults : DefaultMeaning declaration.fallback (lookup declaration.name supplied) effective)
      (value : Meaning declaration.type effective typed)
      (failure : VariablesRejected supplied rest error) :
      VariablesRejected supplied (declaration :: rest) error

theorem variables_rejected_complete (failure : VariablesRejected supplied declarations error) :
    variables supplied declarations = .error error := by
  induction failure with
  | head defaults failure =>
    simp [variables, defaulted_complete defaults, (coerce_rejected _ _ _).mpr failure]
  | tail defaults value failure ih =>
    simp [variables, defaulted_complete defaults, coerce_complete value, ih]

theorem variables_rejected_sound (failure : variables supplied declarations = .error error) :
    VariablesRejected supplied declarations error := by
  induction declarations with
  | nil => cases failure
  | cons declaration rest ih =>
    cases first : coerce declaration.type (defaulted declaration.fallback (lookup declaration.name supplied)) with
    | error code =>
      simp [variables, first] at failure
      cases failure
      exact .head (defaulted_sound _ _) ((coerce_rejected _ _ _).mp first)
    | ok value =>
      cases remaining : variables supplied rest with
      | ok tail => simp [variables, first, remaining] at failure
      | error code =>
        simp [variables, first, remaining] at failure
        cases failure
        exact .tail (defaulted_sound _ _) (coerce_sound _ _ _ first) (ih remaining)

def DefaultValid (declaration : Variable) : Prop :=
  ∀ raw ∈ declaration.fallback, LiteralValid declaration.type raw

instance (declaration : Variable) : Decidable (DefaultValid declaration) := by
  unfold DefaultValid; infer_instance

def hasNonNullDefault (declaration : Variable) : Bool :=
  match declaration.fallback with | none | some .null => false | _ => true

/-- Scalar identity is preserved at variable locations; a non-null default can
permit a nullable declaration at a required location. Explicit null still overrides it. -/
def Usable (declaration : Variable) (location : ScalarType) (locationDefault : Bool := false) : Prop :=
  declaration.type.scalar = location.scalar ∧
    (location.required = false ∨ declaration.type.required = true ∨ hasNonNullDefault declaration = true ∨ locationDefault = true)

instance (declaration : Variable) (location : ScalarType) (locationDefault : Bool) : Decidable (Usable declaration location locationDefault) := by
  unfold Usable; infer_instance

def ExpressionValid (declarations : List Variable) (location : ScalarType) (expression : Expr) : Prop :=
  match expression with
  | .literal raw => LiteralValid location raw
  | .variable name => ∃ declaration ∈ declarations, declaration.name = name ∧ Usable declaration location

instance (declarations : List Variable) (location : ScalarType) (expression : Expr) : Decidable (ExpressionValid declarations location expression) := by
  unfold ExpressionValid; split <;> infer_instance

def usedVariables : Expr → List String
  | .literal _ => []
  | .variable name => [name]

/-- Field coercion is a separate phase; no resolver is invoked here. -/
def argument (type : ScalarType) (fallback : Option Raw) (environment : Environment) (expression : Option Expr) :=
  coerce type (defaulted fallback (expression.bind (eval environment)))

theorem argument_sound (success : argument type fallback environment expression = .ok value) :
    ∃ effective, DefaultMeaning fallback (expression.bind (eval environment)) effective ∧ Meaning type effective value :=
  ⟨_, defaulted_sound _ _, coerce_sound _ _ _ success⟩

theorem argument_complete (defaults : DefaultMeaning fallback (expression.bind (eval environment)) effective)
    (meaning : Meaning type effective value) : argument type fallback environment expression = .ok value := by
  simp only [argument, defaulted_complete defaults, coerce_complete meaning]

end GraphQL.Plan.InputCoercion

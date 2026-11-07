import Example.Tenant.Evaluation
import GraphQL.Plan.Input.Variables

namespace Example.Tenant.InputSurface
open GraphQL.Plan.InputCoercion

/-- Decoded P2 syntax. Excluded features remain explicit until profile validation. -/
inductive Selection where
  | nil
  | field (name : String) (arguments : List (String × Expr)) (children rest : Selection)
  | excluded
  deriving DecidableEq, Repr

structure Operation where
  variables : List Variable
  selection : Selection
  declaredTypes : List (Option ScalarType) := variables.map (fun declaration => some declaration.type)
  deriving DecidableEq, Repr

def skeleton : Selection → PSelection
  | .nil | .excluded => .nil
  | .field name arguments children rest =>
    .field name (arguments.map (fun argument => (argument.1, Literal.string ""))) (skeleton children) (skeleton rest)

def expressionProfile : Expr → Bool
  | .literal .unsupported => false
  | _ => true

def profile : Selection → Prop
  | .nil => True
  | .excluded => False
  | .field _ arguments children rest =>
    (∀ argument ∈ arguments, expressionProfile argument.2 = true) ∧ profile children ∧ profile rest

instance profileDecidable (selection : Selection) : Decidable (profile selection) :=
  match selection with
  | .nil => isTrue trivial
  | .excluded => isFalse id
  | .field _ _ children rest => by
    letI := profileDecidable children
    letI := profileDecidable rest
    unfold profile
    infer_instance

def expressions (declarations : List Variable) : Selection → Prop
  | .nil | .excluded => True
  | .field _ arguments children rest =>
    (∀ argument ∈ arguments, ExpressionValid declarations ⟨.id, true⟩ argument.2) ∧
      expressions declarations children ∧ expressions declarations rest

instance expressionsDecidable (declarations : List Variable) (selection : Selection) : Decidable (expressions declarations selection) :=
  match selection with
  | .nil | .excluded => isTrue trivial
  | .field _ _ children rest => by
    letI := expressionsDecidable declarations children
    letI := expressionsDecidable declarations rest
    unfold expressions
    infer_instance

def used : Selection → List String
  | .nil | .excluded => []
  | .field _ arguments children rest => arguments.flatMap (fun argument => usedVariables argument.2) ++ used children ++ used rest

def nodes : Selection → Nat
  | .nil => 0
  | .excluded => 1
  | .field _ _ children rest => 1 + nodes children + nodes rest

def depth : Selection → Nat
  | .nil => 0
  | .excluded => 1
  | .field _ _ children rest => max (1 + depth children) (depth rest)

/-- These bounds are syntax predicates, not aliases for preparation success. -/
def WithinLimits (operation : Operation) : Prop :=
  operation.variables.length ≤ 32 ∧ nodes operation.selection ≤ 256 ∧ depth operation.selection ≤ 32

instance (operation : Operation) : Decidable (WithinLimits operation) := by unfold WithinLimits; infer_instance

def InProfile (operation : Operation) : Prop := operation.declaredTypes = operation.variables.map (fun declaration => some declaration.type) ∧ profile operation.selection
instance (operation : Operation) : Decidable (InProfile operation) := by unfold InProfile; infer_instance

/-- Domain schema validity comes from S0; expressions and definitions have their
own independent syntactic/type rules. No preparer or generated plan occurs here. -/
def ValidOperation (operation : Operation) : Prop :=
  Example.Tenant.ValidOperation (skeleton operation.selection) ∧
  (operation.variables.map Variable.name).Nodup ∧
  (∀ declaration ∈ operation.variables, DefaultValid declaration) ∧
  expressions operation.variables operation.selection ∧
  (∀ declaration ∈ operation.variables, declaration.name ∈ used operation.selection)

def rootArgument : Selection → Option Expr
  | .nil | .excluded => none
  | .field name arguments _ rest =>
    if name = "project" then lookup "id" arguments else rootArgument rest

/-- Surface input meaning is stated with the independently interpreted key. It
uses only S0 domain meanings and its total field-error completion. -/
def meanings (snapshot : Snapshot) (principal : Principal) (key : Except Error String) : Spec.DomainMeanings snapshot
  | .query, "project", _ => match key with
    | .ok value => match projectOccurrence snapshot principal value with
      | none => .absent
      | some row => .object (.project row)
    | .error _ => .invalid
  | context, name, arguments => Spec.tenantMeanings snapshot principal context name arguments

def Eval (snapshot : Snapshot) (principal : Principal) (operation : Operation) (key : Except Error String) : Spec.Response :=
  Spec.EvalSpec (meanings snapshot principal key) (skeleton operation.selection)

end Example.Tenant.InputSurface

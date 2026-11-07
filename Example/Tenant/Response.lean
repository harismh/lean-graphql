import Example.Tenant.Model
import Example.Tenant.Selection

namespace Example.Tenant.Spec

inductive Shape where
  | scalar (nullable : Bool)
  | object (type : ObjectType) (nullable : Bool)
  | list (type : ObjectType) (nullable elementNullable : Bool)
  deriving DecidableEq, Repr

def Shape.nullable : Shape → Bool
  | .scalar n | .object _ n | .list _ n _ => n

/-- Explicit independent schema table. P1 ID arguments accept string literals only. -/
def fieldShape : ObjectType → String → Option Shape
  | .query, "project" => some (.object .project true)
  | .query, "projects" => some (.list .project false false)
  | .project, "tasks" => some (.list .task false false)
  | .task, "project" => some (.object .project false)
  | .project, "id" | .project, "title" | .task, "id" | .task, "title" =>
    some (.scalar false)
  | _, _ => none

def Shape.childType : Shape → Option ObjectType
  | .scalar _ => none
  | .object type _ | .list type _ _ => some type

theorem object_declaration_has_shape (decl : ObjectField parent name args child) :
    ∃ shape, fieldShape parent name = some shape ∧ shape.childType = some child := by
  cases decl with
  | project => exact ⟨.object .project true, rfl, rfl⟩
  | projects => exact ⟨.list .project false false, rfl, rfl⟩
  | tasks => exact ⟨.list .task false false, rfl, rfl⟩
  | taskProject => exact ⟨.object .project false, rfl, rfl⟩

theorem leaf_declaration_has_shape (decl : LeafField parent name) :
    fieldShape parent name = some (.scalar false) := by cases decl <;> rfl

inductive Segment where
  | field (name : String)
  | index (position : Nat)
  deriving DecidableEq, Repr
abbrev Path := List Segment

structure Error where
  code : PublicError ApplicationError
  path : Path
  deriving DecidableEq, Repr

inductive Value where
  | null
  | string (value : String)
  | object (fields : List (String × Value))
  | array (items : List Value)
  deriving BEq, Repr

inductive Result (α : Type) where
  | ok (value : α) (errors : List Error)
  | bubble (errors : List Error)
  deriving BEq, Repr

def Result.map (f : α → β) : Result α → Result β
  | .ok value errors => .ok (f value) errors
  | .bubble errors => .bubble errors

def Result.errors : Result α → List Error
  | .ok _ es | .bubble es => es

def boundary (nullable : Bool) : Result Value → Result Value
  | .bubble es => if nullable then .ok .null es else .bubble es
  | .ok v es => .ok v es

def pair (f : α → β → γ) : Result α → Result β → Result γ
  | .ok a ea, .ok b eb => .ok (f a b) (ea ++ eb)
  | a, b => .bubble (a.errors ++ b.errors)

def collect : List (Result Value) → Result (List Value)
  | [] => .ok [] []
  | head :: rest => pair List.cons head (collect rest)

def completeList (nullable elementNullable : Bool) (items : List (Result Value)) :=
  boundary nullable ((collect (items.map (boundary elementNullable))).map Value.array)

structure Response where
  data : Value
  errors : List Error
  deriving BEq, Repr

def envelope : Result Value → Response
  | .ok value errors => ⟨value, errors⟩
  | .bubble errors => ⟨.null, errors⟩

theorem nullable_catches (es : List Error) : boundary true (.bubble es) = .ok .null es := rfl
theorem required_propagates (r : Result Value) : boundary false r = r := by cases r <;> rfl
theorem pair_errors (f : α → β → γ) (a : Result α) (b : Result β) :
    (pair f a b).errors = a.errors ++ b.errors := by cases a <;> cases b <;> rfl
theorem boundary_errors (n : Bool) (r : Result Value) : (boundary n r).errors = r.errors := by
  cases r <;> cases n <;> rfl

/-- All four list wrapper combinations, with one failing element. -/
theorem list_nullable_nullable (es : List Error) :
    completeList true true [.bubble es] = .ok (.array [.null]) es := by
  simp [completeList, boundary, collect, pair, Result.map]
theorem list_required_nullable (es : List Error) :
    completeList false true [.bubble es] = .ok (.array [.null]) es := by
  simp [completeList, boundary, collect, pair, Result.map]
theorem list_nullable_required (es : List Error) :
    completeList true false [.bubble es] = .ok .null es := by
  simp [completeList, boundary, collect, pair, Result.map, Result.errors]
theorem list_required_required (es : List Error) :
    completeList false false [.bubble es] = .bubble es := by
  simp [completeList, boundary, collect, pair, Result.map, Result.errors]

end Example.Tenant.Spec

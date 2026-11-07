import Std

namespace Example.Tenant

inductive Literal where
  | string (value : String)
  | int (value : Int)
  | null
  deriving DecidableEq, Repr

/-- First-order surface syntax; no generated field IDs or execution IR. -/
inductive PSelection where
  | nil
  | field (name : String) (arguments : List (String × Literal))
      (children rest : PSelection)
  deriving DecidableEq, Repr

def PSelection.names : PSelection → List String
  | .nil => []
  | .field name _ _ rest => name :: rest.names

inductive ObjectType where
  | query | project | task
  deriving DecidableEq, Repr

/-- The specification's schema declarations, independent of SDL elaboration. -/
inductive ObjectField : ObjectType → String → List (String × Literal) → ObjectType → Prop
  | project (id : String) : ObjectField .query "project" [("id", .string id)] .project
  | projects : ObjectField .query "projects" [] .project
  | tasks : ObjectField .project "tasks" [] .task
  | taskProject : ObjectField .task "project" [] .project

inductive LeafField : ObjectType → String → Prop
  | projectId : LeafField .project "id"
  | projectTitle : LeafField .project "title"
  | taskId : LeafField .task "id"
  | taskTitle : LeafField .task "title"

/-- P1 excludes aliases and repeated fields. Object fields require children;
scalar fields forbid them. Arguments are specified by the field declaration. -/
inductive ValidPSelection : ObjectType → PSelection → Prop
  | nil : ValidPSelection object .nil
  | leaf (decl : LeafField object name) (unique : name ∉ rest.names)
      (tail : ValidPSelection object rest) :
      ValidPSelection object (.field name [] .nil rest)
  | object (decl : ObjectField parent name args child)
      (nonempty : children ≠ .nil) (unique : name ∉ rest.names)
      (nested : ValidPSelection child children) (tail : ValidPSelection parent rest) :
      ValidPSelection parent (.field name args children rest)

def ValidOperation (selection : PSelection) : Prop :=
  selection ≠ .nil ∧ ValidPSelection .query selection

theorem valid_names_unique (h : ValidPSelection object selection) : selection.names.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | leaf _ unique _ ih => exact List.nodup_cons.mpr ⟨unique, ih⟩
  | object _ _ unique _ _ _ ih => exact List.nodup_cons.mpr ⟨unique, ih⟩

theorem no_unknown_root (unknown : name ≠ "project" ∧ name ≠ "projects") :
    ¬ ValidPSelection .query (.field name args children rest) := by
  intro h
  cases h with
  | leaf decl _ _ => cases decl
  | object decl _ _ _ _ =>
    cases decl with
    | project => exact unknown.1 rfl
    | projects => exact unknown.2 rfl

end Example.Tenant

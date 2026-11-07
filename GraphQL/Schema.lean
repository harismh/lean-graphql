import Lean

namespace GraphQL

/-- Non-null is a flag on a named or list reference, so `T!!` is unrepresentable. -/
inductive TypeRef where
  | named (name : String) (required : Bool := false)
  | list (item : TypeRef) (required : Bool := false)
  deriving Repr, DecidableEq, Inhabited

def TypeRef.isRequired : TypeRef → Bool
  | .named _ r | .list _ r => r

def TypeRef.base : TypeRef → String
  | .named n _ => n
  | .list t _ => t.base

def TypeRef.require : TypeRef → TypeRef
  | .named n _ => .named n true
  | .list t _ => .list t true

inductive Kind where
  | scalar | enumType | input | object | interface | union
  deriving Repr, DecidableEq, Inhabited

structure Argument where
  name : String
  type : TypeRef
  deriving Repr, DecidableEq, Inhabited

structure Field where
  name : String
  type : TypeRef
  arguments : List Argument := []
  deriving Repr, DecidableEq, Inhabited

structure TypeDef where
  name : String
  kind : Kind
  fields : List Field := []
  members : List String := []
  implements : List String := []
  deriving Repr, DecidableEq, Inhabited

structure Schema where
  types : List TypeDef
  query : String := "Query"
  deriving Repr, DecidableEq, Inhabited

def Schema.find? (s : Schema) (name : String) : Option TypeDef :=
  s.types.find? (·.name == name)

def Schema.field? (s : Schema) (owner name : String) : Option Field :=
  (s.find? owner).bind (fun t => t.fields.find? (·.name == name))

def builtinScalars : List String := ["String", "ID", "Int", "Boolean"]

def Schema.inputName (s : Schema) (n : String) : Bool :=
  builtinScalars.contains n || (s.find? n).any (fun t =>
    t.kind == .scalar || t.kind == .enumType || t.kind == .input)

def Schema.outputName (s : Schema) (n : String) : Bool :=
  builtinScalars.contains n || (s.find? n).any (fun t => t.kind != .input)

def Schema.objectName (s : Schema) (n : String) : Bool :=
  (s.find? n).any (·.kind == .object)

def Schema.compositeName (s : Schema) (n : String) : Bool :=
  (s.find? n).any (fun t => t.kind == .object || t.kind == .interface || t.kind == .union)

def Schema.possibleType (s : Schema) (expected actual : String) : Bool :=
  if expected == actual then s.objectName actual else
  match s.find? expected with
  | some t =>
    if t.kind == .union then t.members.contains actual && s.objectName actual
    else if t.kind == .interface then
      (s.find? actual).any (fun a => a.kind == .object && a.implements.contains expected)
    else false
  | none => false

def unique (names : List String) : Prop := names.Pairwise (· ≠ ·)
instance (names : List String) : Decidable (unique names) := inferInstanceAs (Decidable (names.Pairwise (· ≠ ·)))

/-- An independent, deliberately scoped predicate: this is NOT full SDL validity.
    The prototype checks names, roots, kinds, references, union membership and exact
    interface-field agreement. Full covariance, defaults and input cycles are later work. -/
def Schema.ValidCore (s : Schema) : Prop :=
  unique (s.types.map (·.name)) ∧
  s.objectName s.query = true ∧
  (∀ t ∈ s.types,
    t.name.isEmpty = false ∧ t.name.startsWith "__" = false ∧
    (builtinScalars ++ ["Float"]).contains t.name = false ∧
    unique (t.fields.map (·.name)) ∧ unique t.members ∧ unique t.implements ∧
    (t.kind = .union → t.members ≠ [] ∧ ∀ n ∈ t.members, s.objectName n = true) ∧
    (t.kind = .enumType → t.members ≠ [] ∧ ∀ n ∈ t.members,
      n.startsWith "__" = false ∧ ["true", "false", "null"].contains n = false) ∧
    ((t.kind = .object ∨ t.kind = .interface ∨ t.kind = .input) → t.fields ≠ []) ∧
    (∀ f ∈ t.fields,
      f.name.startsWith "__" = false ∧
      (t.kind = .input → f.arguments = []) ∧
      (if t.kind = .input then s.inputName f.type.base else s.outputName f.type.base) = true ∧
      unique (f.arguments.map (·.name)) ∧
      (∀ a ∈ f.arguments, a.name.startsWith "__" = false ∧ s.inputName a.type.base = true)) ∧
    (∀ i ∈ t.implements,
      ∃ iface ∈ s.types, iface.name = i ∧ iface.kind = .interface ∧
        ∀ f ∈ iface.fields, f ∈ t.fields))

set_option synthInstance.maxSize 256 in
instance (s : Schema) : Decidable s.ValidCore := by
  unfold Schema.ValidCore
  infer_instance

def checkSchema (s : Schema) : Bool := decide s.ValidCore

/-- Reflection for the predicate decision procedure, not a separate validator proof. -/
theorem checkSchema_sound (s : Schema) (h : checkSchema s = true) : s.ValidCore :=
  of_decide_eq_true h

structure CheckedSchema where
  data : Schema
  valid : data.ValidCore

def Schema.check (s : Schema) : Except String CheckedSchema :=
  if h : s.ValidCore then .ok ⟨s, h⟩
  else .error "schema violates prototype invariants (root, names, field kinds, references or interface agreement)"

end GraphQL

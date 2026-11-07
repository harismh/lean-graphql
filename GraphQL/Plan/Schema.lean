import Std

namespace GraphQL.Plan

inductive Input (α : Type) where
  | omitted
  | null
  | value (data : α)
  deriving DecidableEq, Repr

inductive InputType where
  | unit | string | int | boolean
  | optional (inner : InputType)
  | pair (left right : InputType)
  deriving DecidableEq, Repr

def InputType.denote : InputType → Type
  | .unit => Unit
  | .string => String
  | .int => Int
  | .boolean => Bool
  | .optional t => Input t.denote
  | .pair a b => a.denote × b.denote

inductive OutputType (objects : Nat) where
  | string | int | boolean
  | object (id : Fin objects)
  | nullable (inner : OutputType objects)
  | list (inner : OutputType objects)
  deriving DecidableEq, Repr

def OutputType.denote (models : Fin n → Type) : OutputType n → Type
  | .string => String
  | .int => Int
  | .boolean => Bool
  | .object o => models o
  | .nullable t => Option (t.denote models)
  | .list t => List (t.denote models)

structure FieldDecl (objects : Nat) where
  name : String
  input : InputType
  output : OutputType objects
  deriving DecidableEq, Repr

/-- Declarations are finite; recursive object fields refer to an object index. -/
structure Schema where
  objectCount : Nat
  fields : Fin objectCount → List (FieldDecl objectCount)

structure FieldId (schema : Schema) (object : Fin schema.objectCount) where
  index : Fin (schema.fields object).length

def FieldId.decl (f : FieldId schema object) := (schema.fields object)[f.index]
abbrev FieldId.Args (f : FieldId schema object) := f.decl.input.denote
abbrev FieldId.Out (f : FieldId schema object) (models : Fin schema.objectCount → Type) :=
  f.decl.output.denote models

inductive FrameworkError where
  | argument | exhausted | internal
  deriving DecidableEq, Repr
inductive PublicError (app : Type) where
  | framework (error : FrameworkError)
  | application (error : app)
  deriving DecidableEq, Repr
abbrev Outcome (app result : Type) := Except (PublicError app) result

inductive Call (schema : Schema) (models : Fin schema.objectCount → Type) (scope : Type) where
  | one {object : Fin schema.objectCount} (field : FieldId schema object)
      (context : scope) (parent : models object) (args : field.Args)
  | batch {object : Fin schema.objectCount} (field : FieldId schema object)
      (context : scope) {n : Nat} (inputs : Vector (models object × field.Args) n)

def Answer (app : Type) : Call schema models scope → Type
  | .one f _ _ _ => Outcome app (f.Out models)
  | .batch f _ (n := n) _ => Vector (Outcome app (f.Out models)) n

abbrev Meanings (schema : Schema) (models : Fin schema.objectCount → Type) (scope app : Type) :=
  {object : Fin schema.objectCount} → (field : FieldId schema object) →
    scope → models object → field.Args → Outcome app (field.Out models)

structure Contracts (schema : Schema) (models : Fin schema.objectCount → Type) (scope app : Type) where
  pre : {o : Fin schema.objectCount} → (f : FieldId schema o) → scope → models o → f.Args → Prop
  post : {o : Fin schema.objectCount} → (f : FieldId schema o) → scope → models o → f.Args →
    Outcome app (f.Out models) → Prop
  compatible : {o : Fin schema.objectCount} → (f : FieldId schema o) → scope →
    {n : Nat} → Vector (models o × f.Args) n → Prop

def Contracts.Pre (spec : Contracts schema models scope app) : Call schema models scope → Prop
  | .one f ctx parent args => spec.pre f ctx parent args
  | .batch f ctx inputs => spec.compatible f ctx inputs ∧
      ∀ i, spec.pre f ctx (inputs.get i).1 (inputs.get i).2

def Contracts.Post (spec : Contracts schema models scope app) (call : Call schema models scope) :
    Answer app call → Prop :=
  match call with
  | .one f ctx parent args => spec.post f ctx parent args
  | .batch f ctx inputs => fun results =>
      ∀ i, spec.post f ctx (inputs.get i).1 (inputs.get i).2 (results.get i)

theorem omitted_ne_null : (Input.omitted : Input α) ≠ .null := by intro h; cases h

theorem field_lookup_exact (f : FieldId schema object) :
    f.decl = (schema.fields object)[f.index] := rfl

end GraphQL.Plan

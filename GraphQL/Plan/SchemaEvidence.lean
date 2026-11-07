import GraphQL.Schema
import GraphQL.Plan.Schema

namespace GraphQL.Plan

/-- P1 binding profile: scalar arguments, recursive object/list outputs. -/
def inputEncoding : GraphQL.TypeRef → Option InputType
  | .named name required => do
    let base ← match name with
      | "String" | "ID" => some .string
      | "Int" => some .int
      | "Boolean" => some .boolean
      | _ => none
    return if required then base else .optional base
  | .list .. => none

def argumentsEncoding : List GraphQL.Argument → Option InputType
  | [] => some .unit
  | [arg] => inputEncoding arg.type
  | arg :: rest => do return .pair (← inputEncoding arg.type) (← argumentsEncoding rest)

def objectIndex (ast : GraphQL.Schema) (name : String) : Option (Fin ast.types.length) :=
  (List.finRange ast.types.length).find? (fun i => ast.types[i].name == name && ast.types[i].kind == .object)

def outputEncoding (ast : GraphQL.Schema) : GraphQL.TypeRef → Option (OutputType ast.types.length)
  | .named name required => do
    let base ← match name with
      | "String" | "ID" => some .string
      | "Int" => some .int
      | "Boolean" => some .boolean
      | _ => (objectIndex ast name).map OutputType.object
    return if required then base else .nullable base
  | .list item required => do
    let base := OutputType.list (← outputEncoding ast item)
    return if required then base else .nullable base

/-- Deliberately excludes abstract/input types, custom scalars and input lists.
This strengthens ValidCore only for the binding profile, not full GraphQL validity. -/
def WellFormedSchema (ast : GraphQL.Schema) : Prop :=
  ast.ValidCore ∧ ∀ object ∈ ast.types,
    object.kind = .object ∧ object.members = [] ∧ object.implements = [] ∧
    ∀ field ∈ object.fields,
      field.name ≠ "" ∧ (∀ arg ∈ field.arguments, arg.name ≠ "") ∧
      (argumentsEncoding field.arguments).isSome = true ∧ (outputEncoding ast field.type).isSome = true

instance (ast : GraphQL.Schema) : Decidable (WellFormedSchema ast) := by
  unfold WellFormedSchema
  infer_instance

/-- Object coordinates are the AST's declaration coordinates, never an emitted permutation. -/
structure IndexedSchema (ast : GraphQL.Schema) where
  fields : Fin ast.types.length → List (FieldDecl ast.types.length)
  root : Fin ast.types.length
  argumentLayouts : Fin ast.types.length → Nat → List GraphQL.Argument

abbrev IndexedSchema.schema (indexed : IndexedSchema ast) : Schema := ⟨ast.types.length, indexed.fields⟩

def FieldRepresents (ast : GraphQL.Schema) (raw : GraphQL.Field) (typed : FieldDecl ast.types.length) (layout : List GraphQL.Argument) : Prop :=
  raw.name = typed.name ∧ argumentsEncoding raw.arguments = some typed.input ∧
    outputEncoding ast raw.type = some typed.output ∧ raw.arguments = layout

instance (ast : GraphQL.Schema) (raw : GraphQL.Field) (typed : FieldDecl ast.types.length) (layout : List GraphQL.Argument) :
    Decidable (FieldRepresents ast raw typed layout) := by unfold FieldRepresents; infer_instance

def AtFieldRepresents (ast : GraphQL.Schema) (raw : Option GraphQL.Field)
    (typed : FieldDecl ast.types.length) (layout : List GraphQL.Argument) : Prop :=
  match raw with | none => False | some field => FieldRepresents ast field typed layout

instance (ast : GraphQL.Schema) (raw : Option GraphQL.Field) (typed : FieldDecl ast.types.length) (layout : List GraphQL.Argument) :
    Decidable (AtFieldRepresents ast raw typed layout) := by
  cases raw <;> dsimp [AtFieldRepresents] <;> infer_instance

/-- Independent per-object certificate, suitable for bounded generated proof artifacts. -/
def ObjectRepresents (ast : GraphQL.Schema) (indexed : IndexedSchema ast) (owner : Fin ast.types.length) : Prop :=
  ast.types[owner].fields.length = (indexed.fields owner).length ∧
    ∀ field : Fin (indexed.fields owner).length,
      AtFieldRepresents ast ast.types[owner].fields[field.val]? (indexed.fields owner)[field] (indexed.argumentLayouts owner field.val)

instance (ast : GraphQL.Schema) (indexed : IndexedSchema ast) (owner : Fin ast.types.length) :
    Decidable (ObjectRepresents ast indexed owner) := by unfold ObjectRepresents; infer_instance

/-- Independent coordinate-by-coordinate agreement, checked on an explicit artifact. -/
def Represents (ast : GraphQL.Schema) (indexed : IndexedSchema ast) : Prop :=
  ast.types[indexed.root].name = ast.query ∧ ∀ owner, ObjectRepresents ast indexed owner

theorem represents_of_objects (root : ast.types[indexed.root].name = ast.query)
    (objects : ∀ owner, ObjectRepresents ast indexed owner) : Represents ast indexed := ⟨root, objects⟩

instance (ast : GraphQL.Schema) (indexed : IndexedSchema ast) : Decidable (Represents ast indexed) := by
  unfold Represents
  infer_instance

structure CheckedIndexed (ast : GraphQL.Schema) where
  indexed : IndexedSchema ast
  wellFormed : WellFormedSchema ast
  represents : Represents ast indexed

abbrev CanonicalField (ast : GraphQL.Schema) (owner : Fin ast.types.length) :=
  Fin ast.types[owner].fields.length

def CheckedIndexed.field (checked : CheckedIndexed ast) (owner : Fin ast.types.length)
    (field : CanonicalField ast owner) : FieldId checked.indexed.schema owner :=
  ⟨⟨field.val, by rw [← (checked.represents.2 owner).1]; exact field.isLt⟩⟩

def CheckedIndexed.coordinate (checked : CheckedIndexed ast)
    (field : FieldId checked.indexed.schema owner) : CanonicalField ast owner :=
  ⟨field.index.val, by rw [(checked.represents.2 owner).1]; exact field.index.isLt⟩

theorem canonical_roundtrip (checked : CheckedIndexed ast) (owner : Fin ast.types.length)
    (field : CanonicalField ast owner) : checked.coordinate (checked.field owner field) = field := rfl

theorem field_roundtrip (checked : CheckedIndexed ast) (field : FieldId checked.indexed.schema owner) :
    checked.field owner (checked.coordinate field) = field := by cases field; rfl

theorem canonical_field_represents (checked : CheckedIndexed ast) (owner : Fin ast.types.length)
    (field : CanonicalField ast owner) :
    FieldRepresents ast ast.types[owner].fields[field] (checked.field owner field).decl (checked.indexed.argumentLayouts owner field.val) := by
  have h := (checked.represents.2 owner).2 (checked.field owner field).index
  simpa [CheckedIndexed.field, FieldId.decl, AtFieldRepresents] using h

def checkIndexed (ast : GraphQL.Schema) (indexed : IndexedSchema ast) : Option (CheckedIndexed ast) :=
  if hw : WellFormedSchema ast then
    if hr : Represents ast indexed then some ⟨indexed, hw, hr⟩ else none
  else none

theorem check_indexed_sound (h : checkIndexed ast indexed = some checked) :
    WellFormedSchema ast ∧ Represents ast indexed := by
  unfold checkIndexed at h
  split at h
  · rename_i hw
    split at h
    · rename_i hr
      exact ⟨hw, hr⟩
    · contradiction
  · contradiction

end GraphQL.Plan

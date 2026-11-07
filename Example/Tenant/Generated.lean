import Example.Tenant.Bindings
import GraphQL.Plan.Arguments
import GraphQL.Plan.Bindings

namespace Example.Tenant.Generated
open GraphQL.Plan

-- Generated artifact. Regenerate; do not edit the semantic anchor or implementations.
set_option maxRecDepth 30000
set_option maxHeartbeats 16000000

abbrev ast : GraphQL.Schema := Example.Tenant.Binding.demoAst
def emittedAst : GraphQL.Schema := ⟨[⟨"Query", .object, [⟨"project", (.named "Project" false), [⟨"id", (.named "ID" true)⟩]⟩, ⟨"projects", (.list (.named "Project" true) true), []⟩], [], []⟩, ⟨"Project", .object, [⟨"id", (.named "ID" true), []⟩, ⟨"title", (.named "String" true), []⟩, ⟨"tasks", (.list (.named "Task" true) true), []⟩], [], []⟩, ⟨"Task", .object, [⟨"id", (.named "ID" true), []⟩, ⟨"title", (.named "String" true), []⟩, ⟨"project", (.named "Project" true), []⟩], [], []⟩], "Query"⟩
theorem source_anchor : emittedAst = ast := by decide +kernel

def indexed : IndexedSchema ast := ⟨(fun owner => match owner.val with
  | 0 => [⟨"project", .string, (.nullable (.object 1))⟩, ⟨"projects", .unit, (.list (.object 1))⟩]
  | 1 => [⟨"id", .unit, .string⟩, ⟨"title", .unit, .string⟩, ⟨"tasks", .unit, (.list (.object 2))⟩]
  | _ => [⟨"id", .unit, .string⟩, ⟨"title", .unit, .string⟩, ⟨"project", .unit, (.object 1)⟩]), 0, (fun owner field => match owner.val, field with
  | 0, 0 => [⟨"id", (.named "ID" true)⟩]
  | 0, 1 => []
  | 1, 0 => []
  | 1, 1 => []
  | 1, 2 => []
  | 2, 0 => []
  | 2, 1 => []
  | 2, 2 => []
  | _, _ => [])⟩
theorem well_formed : WellFormedSchema ast := by decide +kernel
theorem represents : Represents ast indexed := by decide +kernel
abbrev checked : CheckedIndexed ast := ⟨indexed, well_formed, represents⟩

abbrev Args_0_0 := ArgumentRecord (ast.types[0].fields[0].arguments)
def Args_0_0.pack (value : (checked.field 0 ⟨0, by decide⟩).Args) : Args_0_0 := packArguments _ value
def Args_0_0.unpack (record : Args_0_0) : (checked.field 0 ⟨0, by decide⟩).Args := unpackArguments _ record
theorem Args_0_0_projection : ArgumentProjectionAgreement (ast.types[0].fields[0].arguments) Args_0_0.pack := canonical_argument_projection _
theorem Args_0_0_roundtrip (value : (checked.field 0 ⟨0, by decide⟩).Args) : Args_0_0.unpack (Args_0_0.pack value) = value  := unpack_pack_arguments (ast.types[0].fields[0].arguments) value
theorem Args_0_0_inverse (record : Args_0_0) : Args_0_0.pack (Args_0_0.unpack record) = record := pack_unpack_arguments (ast.types[0].fields[0].arguments) record
def Args_0_0.arg_0_id : NamedArgument (ast.types[0].fields[0].arguments) "id" := ⟨⟨0, by decide⟩, rfl⟩
abbrev Args_0_1 := ArgumentRecord (ast.types[0].fields[1].arguments)
def Args_0_1.pack (value : (checked.field 0 ⟨1, by decide⟩).Args) : Args_0_1 := packArguments _ value
def Args_0_1.unpack (record : Args_0_1) : (checked.field 0 ⟨1, by decide⟩).Args := unpackArguments _ record
theorem Args_0_1_projection : ArgumentProjectionAgreement (ast.types[0].fields[1].arguments) Args_0_1.pack := canonical_argument_projection _
theorem Args_0_1_roundtrip (value : (checked.field 0 ⟨1, by decide⟩).Args) : Args_0_1.unpack (Args_0_1.pack value) = value  := unpack_pack_arguments (ast.types[0].fields[1].arguments) value
theorem Args_0_1_inverse (record : Args_0_1) : Args_0_1.pack (Args_0_1.unpack record) = record := pack_unpack_arguments (ast.types[0].fields[1].arguments) record
abbrev Args_1_0 := ArgumentRecord (ast.types[1].fields[0].arguments)
def Args_1_0.pack (value : (checked.field 1 ⟨0, by decide⟩).Args) : Args_1_0 := packArguments _ value
def Args_1_0.unpack (record : Args_1_0) : (checked.field 1 ⟨0, by decide⟩).Args := unpackArguments _ record
theorem Args_1_0_projection : ArgumentProjectionAgreement (ast.types[1].fields[0].arguments) Args_1_0.pack := canonical_argument_projection _
theorem Args_1_0_roundtrip (value : (checked.field 1 ⟨0, by decide⟩).Args) : Args_1_0.unpack (Args_1_0.pack value) = value  := unpack_pack_arguments (ast.types[1].fields[0].arguments) value
theorem Args_1_0_inverse (record : Args_1_0) : Args_1_0.pack (Args_1_0.unpack record) = record := pack_unpack_arguments (ast.types[1].fields[0].arguments) record
abbrev Args_1_1 := ArgumentRecord (ast.types[1].fields[1].arguments)
def Args_1_1.pack (value : (checked.field 1 ⟨1, by decide⟩).Args) : Args_1_1 := packArguments _ value
def Args_1_1.unpack (record : Args_1_1) : (checked.field 1 ⟨1, by decide⟩).Args := unpackArguments _ record
theorem Args_1_1_projection : ArgumentProjectionAgreement (ast.types[1].fields[1].arguments) Args_1_1.pack := canonical_argument_projection _
theorem Args_1_1_roundtrip (value : (checked.field 1 ⟨1, by decide⟩).Args) : Args_1_1.unpack (Args_1_1.pack value) = value  := unpack_pack_arguments (ast.types[1].fields[1].arguments) value
theorem Args_1_1_inverse (record : Args_1_1) : Args_1_1.pack (Args_1_1.unpack record) = record := pack_unpack_arguments (ast.types[1].fields[1].arguments) record
abbrev Args_1_2 := ArgumentRecord (ast.types[1].fields[2].arguments)
def Args_1_2.pack (value : (checked.field 1 ⟨2, by decide⟩).Args) : Args_1_2 := packArguments _ value
def Args_1_2.unpack (record : Args_1_2) : (checked.field 1 ⟨2, by decide⟩).Args := unpackArguments _ record
theorem Args_1_2_projection : ArgumentProjectionAgreement (ast.types[1].fields[2].arguments) Args_1_2.pack := canonical_argument_projection _
theorem Args_1_2_roundtrip (value : (checked.field 1 ⟨2, by decide⟩).Args) : Args_1_2.unpack (Args_1_2.pack value) = value  := unpack_pack_arguments (ast.types[1].fields[2].arguments) value
theorem Args_1_2_inverse (record : Args_1_2) : Args_1_2.pack (Args_1_2.unpack record) = record := pack_unpack_arguments (ast.types[1].fields[2].arguments) record
abbrev Args_2_0 := ArgumentRecord (ast.types[2].fields[0].arguments)
def Args_2_0.pack (value : (checked.field 2 ⟨0, by decide⟩).Args) : Args_2_0 := packArguments _ value
def Args_2_0.unpack (record : Args_2_0) : (checked.field 2 ⟨0, by decide⟩).Args := unpackArguments _ record
theorem Args_2_0_projection : ArgumentProjectionAgreement (ast.types[2].fields[0].arguments) Args_2_0.pack := canonical_argument_projection _
theorem Args_2_0_roundtrip (value : (checked.field 2 ⟨0, by decide⟩).Args) : Args_2_0.unpack (Args_2_0.pack value) = value  := unpack_pack_arguments (ast.types[2].fields[0].arguments) value
theorem Args_2_0_inverse (record : Args_2_0) : Args_2_0.pack (Args_2_0.unpack record) = record := pack_unpack_arguments (ast.types[2].fields[0].arguments) record
abbrev Args_2_1 := ArgumentRecord (ast.types[2].fields[1].arguments)
def Args_2_1.pack (value : (checked.field 2 ⟨1, by decide⟩).Args) : Args_2_1 := packArguments _ value
def Args_2_1.unpack (record : Args_2_1) : (checked.field 2 ⟨1, by decide⟩).Args := unpackArguments _ record
theorem Args_2_1_projection : ArgumentProjectionAgreement (ast.types[2].fields[1].arguments) Args_2_1.pack := canonical_argument_projection _
theorem Args_2_1_roundtrip (value : (checked.field 2 ⟨1, by decide⟩).Args) : Args_2_1.unpack (Args_2_1.pack value) = value  := unpack_pack_arguments (ast.types[2].fields[1].arguments) value
theorem Args_2_1_inverse (record : Args_2_1) : Args_2_1.pack (Args_2_1.unpack record) = record := pack_unpack_arguments (ast.types[2].fields[1].arguments) record
abbrev Args_2_2 := ArgumentRecord (ast.types[2].fields[2].arguments)
def Args_2_2.pack (value : (checked.field 2 ⟨2, by decide⟩).Args) : Args_2_2 := packArguments _ value
def Args_2_2.unpack (record : Args_2_2) : (checked.field 2 ⟨2, by decide⟩).Args := unpackArguments _ record
theorem Args_2_2_projection : ArgumentProjectionAgreement (ast.types[2].fields[2].arguments) Args_2_2.pack := canonical_argument_projection _
theorem Args_2_2_roundtrip (value : (checked.field 2 ⟨2, by decide⟩).Args) : Args_2_2.unpack (Args_2_2.pack value) = value  := unpack_pack_arguments (ast.types[2].fields[2].arguments) value
theorem Args_2_2_inverse (record : Args_2_2) : Args_2_2.pack (Args_2_2.unpack record) = record := pack_unpack_arguments (ast.types[2].fields[2].arguments) record

-- Internal plumbing: supported application input is BindingsByField via fromCanonical.
structure Resolvers where
  gql_0_0_Query_project : FieldBinding (checked.field 0 ⟨0, by decide⟩) Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError
  gql_0_1_Query_projects : FieldBinding (checked.field 0 ⟨1, by decide⟩) Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError
  gql_1_0_Project_id : FieldBinding (checked.field 1 ⟨0, by decide⟩) Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError
  gql_1_1_Project_title : FieldBinding (checked.field 1 ⟨1, by decide⟩) Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError
  gql_1_2_Project_tasks : FieldBinding (checked.field 1 ⟨2, by decide⟩) Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError
  gql_2_0_Task_id : FieldBinding (checked.field 2 ⟨0, by decide⟩) Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError
  gql_2_1_Task_title : FieldBinding (checked.field 2 ⟨1, by decide⟩) Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError
  gql_2_2_Task_project : FieldBinding (checked.field 2 ⟨2, by decide⟩) Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError

def fromCanonical (bindings : BindingsByField checked Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError) : Resolvers :=
  ⟨bindings 0 ⟨0, by decide⟩, bindings 0 ⟨1, by decide⟩, bindings 1 ⟨0, by decide⟩, bindings 1 ⟨1, by decide⟩, bindings 1 ⟨2, by decide⟩, bindings 2 ⟨0, by decide⟩, bindings 2 ⟨1, by decide⟩, bindings 2 ⟨2, by decide⟩⟩

def adapter (resolvers : Resolvers) : Adapter indexed.schema Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError :=
  fun {owner} field => match owner, field with
  | ⟨0, _⟩, ⟨⟨0, _⟩⟩ => resolvers.gql_0_0_Query_project
  | ⟨0, _⟩, ⟨⟨1, _⟩⟩ => resolvers.gql_0_1_Query_projects
  | ⟨0, _⟩, ⟨⟨n + 2, h⟩⟩ => False.elim (by simp [indexed, ast] at h <;> omega)
  | ⟨1, _⟩, ⟨⟨0, _⟩⟩ => resolvers.gql_1_0_Project_id
  | ⟨1, _⟩, ⟨⟨1, _⟩⟩ => resolvers.gql_1_1_Project_title
  | ⟨1, _⟩, ⟨⟨2, _⟩⟩ => resolvers.gql_1_2_Project_tasks
  | ⟨1, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [indexed, ast] at h <;> omega)
  | ⟨2, _⟩, ⟨⟨0, _⟩⟩ => resolvers.gql_2_0_Task_id
  | ⟨2, _⟩, ⟨⟨1, _⟩⟩ => resolvers.gql_2_1_Task_title
  | ⟨2, _⟩, ⟨⟨2, _⟩⟩ => resolvers.gql_2_2_Task_project
  | ⟨2, _⟩, ⟨⟨n + 3, h⟩⟩ => False.elim (by simp [indexed, ast] at h <;> omega)
  | ⟨n + 3, h⟩, _ => False.elim (by simp at h <;> omega)

-- Descriptive only: no agreement theorem depends on this emitted metadata.
def dispatchMetadata : List (Nat × Nat × String) := [(0, 0, "project"), (0, 1, "projects"), (1, 0, "id"), (1, 1, "title"), (1, 2, "tasks"), (2, 0, "id"), (2, 1, "title"), (2, 2, "project")]

theorem adapter_agreement (bindings : BindingsByField checked Example.Tenant.Binding.carriers Example.Tenant.Binding.Request Example.Tenant.ApplicationError) :
    BindingAgreement bindings (adapter (fromCanonical bindings)) := by
  intro owner field
  rcases owner with ⟨owner, bound⟩
  rcases field with ⟨field, valid⟩
  rcases owner with _ | (_ | (_ | (index))) <;>
    rcases field with _ | (_ | (_ | (index))) <;>
    first | rfl | simp [ast] at bound valid <;> omega

def application : Resolvers := fromCanonical Example.Tenant.Binding.independentBindings
theorem application_agreement : BindingAgreement (checked := checked) Example.Tenant.Binding.independentBindings (adapter application) :=
  adapter_agreement Example.Tenant.Binding.independentBindings

end Example.Tenant.Generated

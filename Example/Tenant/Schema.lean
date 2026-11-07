import GraphQL.Syntax
import GraphQL.Plan.SchemaEvidence
import Example.Tenant.PlanSchema

namespace Example.Tenant.Binding
open GraphQL.Plan

def demoSDL : String := "type Query { project(id: ID!): Project projects: [Project!]! } type Project { id: ID! title: String! tasks: [Task!]! } type Task { id: ID! title: String! project: Project! }"

/-- Readable parsed AST, independent of the adapter/record layout. -/
abbrev demoAst : GraphQL.Schema := ⟨[
  ⟨"Query", .object, [
    ⟨"project", .named "Project" false, [⟨"id", .named "ID" true⟩]⟩,
    ⟨"projects", .list (.named "Project" true) true, []⟩], [], []⟩,
  ⟨"Project", .object, [
    ⟨"id", .named "ID" true, []⟩, ⟨"title", .named "String" true, []⟩,
    ⟨"tasks", .list (.named "Task" true) true, []⟩], [], []⟩,
  ⟨"Task", .object, [
    ⟨"id", .named "ID" true, []⟩, ⟨"title", .named "String" true, []⟩,
    ⟨"project", .named "Project" true, []⟩], [], []⟩], "Query"⟩

/-- Parser-to-readable-AST equality is checked by Tests/TenantSDL.lean, not assumed as a theorem. -/
def parsedDemo := GraphQL.parseSchema demoSDL

def indexedSchema : IndexedSchema demoAst := ⟨Planning.schema.fields, 0, fun owner field =>
  if owner.val = 0 ∧ field = 0 then [⟨"id", .named "ID" true⟩] else []⟩

theorem demo_well_formed : WellFormedSchema demoAst := by decide +kernel

theorem demo_represents : Represents demoAst indexedSchema := by decide +kernel

abbrev checked : CheckedIndexed demoAst := ⟨indexedSchema, demo_well_formed, demo_represents⟩

/-- These identities come from checked AST coordinates, not generated dispatch metadata. -/
abbrev rootProject := checked.field 0 ⟨0, by decide⟩
abbrev rootProjects := checked.field 0 ⟨1, by decide⟩
abbrev projectId := checked.field 1 ⟨0, by decide⟩
abbrev projectTitle := checked.field 1 ⟨1, by decide⟩
abbrev projectTasks := checked.field 1 ⟨2, by decide⟩
abbrev taskId := checked.field 2 ⟨0, by decide⟩
abbrev taskTitle := checked.field 2 ⟨1, by decide⟩
abbrev taskProject := checked.field 2 ⟨2, by decide⟩

theorem title_identity : demoAst.types[1].fields[1].name = projectTitle.decl.name ∧
    projectTitle.decl.name = "title" := ⟨(canonical_field_represents checked 1 ⟨1, by decide⟩).1, rfl⟩

theorem task_project_identity : demoAst.types[2].fields[2].name = taskProject.decl.name ∧
    taskProject.decl.name = "project" := ⟨(canonical_field_represents checked 2 ⟨2, by decide⟩).1, rfl⟩

end Example.Tenant.Binding

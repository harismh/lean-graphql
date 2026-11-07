import GraphQL.Plan.Arguments
import GraphQL.Plan.Bindings

namespace GraphQL.Plan

/-- The record layout is read from the independently checked AST coordinate. -/
def checkedArguments (checked : CheckedIndexed ast) (owner : Fin ast.types.length)
    (field : CanonicalField ast owner) (args : (checked.field owner field).Args) :
    ArgumentRecord ast.types[owner].fields[field].arguments :=
  packArguments _ (cast (congrArg InputType.denote (arguments_encoding_code _ _
    (canonical_field_represents checked owner field).2.1)) args)

/-- Applications consume named records; positional conversion belongs to this
checked library boundary. Optional batch capabilities can be added separately. -/
def namedFieldBinding (checked : CheckedIndexed ast) (owner : Fin ast.types.length)
    (field : CanonicalField ast owner) {models : Fin ast.types.length → Type}
    (resolve : scope → models owner → ArgumentRecord ast.types[owner].fields[field].arguments →
      Outcome app ((checked.field owner field).Out models)) :
    FieldBinding (checked.field owner field) models scope app :=
  ⟨fun context parent args => resolve context parent (checkedArguments checked owner field args), none⟩

theorem named_binding_single (checked : CheckedIndexed ast) (owner : Fin ast.types.length)
    (field : CanonicalField ast owner) {models : Fin ast.types.length → Type}
    (resolve : scope → models owner → ArgumentRecord ast.types[owner].fields[field].arguments →
      Outcome app ((checked.field owner field).Out models)) (context : scope) (parent : models owner)
    (args : (checked.field owner field).Args) :
    (namedFieldBinding checked owner field resolve).single context parent args =
      resolve context parent (checkedArguments checked owner field args) := rfl

end GraphQL.Plan

import Example.Tenant.Compile
open GraphQL.Plan Example.Tenant Example.Tenant.Planning
abbrev otherSchema : Schema := ⟨1, fun _ => [⟨"foreign", .unit, .string⟩]⟩
def wrong : FieldId otherSchema 0 := branchId IR.Branch.project

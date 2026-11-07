import Example.Tenant.Compile
open GraphQL.Plan Example.Tenant Example.Tenant.Planning
def request : Call schema (models ⟨[], []⟩) Principal :=
  .batch (branchId IR.Branch.projects) ⟨1⟩ #v[((), ()), ((), ())]
def wrong : Answer ApplicationError request := #v[(Except.ok [] : Outcome ApplicationError (List (Occurrence ([] : List Project))))]

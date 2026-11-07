import Example.Tenant.S6aProofs
open GraphQL.Plan Example.Tenant
example (failure : TransportFailure) : Answer ApplicationError
    (Call.batch (models := Binding.carriers) (scope := Binding.Request) Binding.rootProjects S4bProofs.request (Vector.replicate 2 ((), ()))) := failure

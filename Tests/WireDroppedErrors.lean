import Example.Tenant.S6cProofs
open Example.Tenant
example : Wire.ResponseMeaning S6cProofs.failure (.object [("data", .null)]) :=
  False.elim (S6cProofs.dropped_errors_rejected (.success .null))

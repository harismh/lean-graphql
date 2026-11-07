import Example.Tenant.S5Proofs
open Example.Tenant
example : InputSurface.ValidOperation { S5Proofs.operation with variables := [] } := by decide +kernel

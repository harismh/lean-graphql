import Example.Tenant.S6bProofs
open Example.Tenant
example : S6bProofs.faultRun.1.val.errors = [] := by decide +kernel

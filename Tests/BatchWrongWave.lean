import Example.Tenant.S4bProofs
open GraphQL.Plan Example.Tenant.S4bProofs Example.Tenant.Batching
example : runMachine (Batch.driver adapter) wrongPositionWave =
    runMachine (Batch.driver adapter) (Batch.rowsWave generatedCapability request (rows prepared) 2 (by decide)) := by rfl

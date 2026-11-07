import Example.Tenant.S6dProofs

namespace Example.Tenant.Demo

def _root_.main (args : List String) : IO Unit := do
  if args == ["--batch-benchmark"] then
    let resolve := GraphQL.Plan.Batch.driver S4bProofs.adapter
    let reference := (GraphQL.Plan.Batch.runCount resolve (Batching.sequential S4bProofs.request S4bProofs.prepared)).2
    let unique := GraphQL.Plan.Batch.uniqueCount Batching.generatedCapability S4bProofs.request
      (GraphQL.Plan.Batch.rowInputs (Batching.rows S4bProofs.prepared))
    for capacity in [1, 2, 3, 4] do
      if positive : 0 < capacity then
        let optimized := (GraphQL.Plan.Batch.runCount resolve (GraphQL.Plan.Batch.rowsWave
          Batching.generatedCapability S4bProofs.request (Batching.rows S4bProofs.prepared) capacity positive)).2
        let wholeOptimized := (GraphQL.Plan.Batch.runCount resolve
          (Batching.execute S4bProofs.adapter S4bProofs.request S4bProofs.selected capacity positive)).2
        let wholeReference := (GraphQL.Plan.Batch.runCount resolve
          (Runtime.execute S4bProofs.request S4bProofs.selected)).2
        IO.println s!"capacity={capacity},unique={unique},reference={reference},optimized={optimized},whole_reference={wholeReference},whole_optimized={wholeOptimized}"
    return
  S5Proofs.nativeTests
  S6aProofs.nativeTests
  S6bProofs.nativeTests
  S6cProofs.nativeTests
  S6dProofs.nativeTests
  let optimized := GraphQL.Plan.runMachine (GraphQL.Plan.Batch.driver S4bProofs.adapter)
    (Batching.execute S4bProofs.adapter S4bProofs.request S4bProofs.selected 2 (by decide))
  unless optimized == Runtime.run S4bProofs.adapter S4bProofs.request S4bProofs.selected do
    throw (IO.userError "optimized P1 native response regression")
  let resolve := GraphQL.Plan.Batch.driver S4bProofs.adapter
  let before := (GraphQL.Plan.Batch.runCount resolve (Runtime.execute S4bProofs.request S4bProofs.selected)).2
  let after := (GraphQL.Plan.Batch.runCount resolve
    (Batching.execute S4bProofs.adapter S4bProofs.request S4bProofs.selected 2 (by decide))).2
  unless after < before do throw (IO.userError "batching must reduce whole-program primitive calls on this fixture")
  IO.println s!"Certified batching: {before} -> {after} total Machine calls on this workload."
  let request := S4Proofs.request
  let selected := S1Proofs.success
  IO.println "P1 typed plan: { projects { title } }"
  let success := Runtime.run (Generated.adapter Generated.application) request selected
  unless success == S0Proofs.successResponse do throw (IO.userError "P1 native execution regression")
  IO.println (reprStr success)
  IO.println "Same executable plan with a permitted resolver fault:"
  IO.println (reprStr (GraphQL.Plan.runMachine (GraphQL.Plan.denoteCall S4Proofs.titleFaults)
    (Runtime.execute request selected)))
  IO.println "Independent items(first: 2) plan:"
  IO.println (reprStr (GraphQL.Plan.runMachine (GraphQL.Plan.denoteCall GraphQL.Plan.ItemsExample.backend)
    (GraphQL.Plan.ItemsExample.execute ["a", "b", "c"] (.value 2) S4Proofs.itemPath)))

end Example.Tenant.Demo

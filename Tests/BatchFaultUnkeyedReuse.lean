import Example.Tenant.S6bProofs
open Example.Tenant Example.Tenant.Planning
example (left : Fault.Post (branchId .taskProject) S6bProofs.request ⟨"t1", 1, "one", "shared"⟩ () (.ok S4bProofs.firstTarget)) :
    Fault.Post (branchId .taskProject) S6bProofs.request ⟨"t3", 1, "three", "missing"⟩ () (.ok S4bProofs.firstTarget) := left

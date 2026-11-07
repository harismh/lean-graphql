import Example.Tenant.CertifiedHandler
open Example.Tenant Handler Protocol
example (request : Protocol.Request) (ready : Ready) (accepted : prepareRequest request = .ok ready)
    (principal : {principal : Principal // DemoAuthSound request.credential principal})
    (result : CoreReply ready ⟨S4bProofs.otherRequest.snapshot, principal.val⟩) :
    CertifiedReply DemoAuthSound DemoAcquireSound request :=
  promote DemoAuthSound DemoAcquireSound request ready accepted principal
    ⟨S4bProofs.otherRequest.snapshot, by
      change S4bProofs.otherRequest.snapshot = S4bProofs.request.snapshot
      decide +kernel⟩ result

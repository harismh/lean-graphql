import Example.Tenant.CertifiedHandler
open Example.Tenant Handler
example : Authenticate Id DemoAuthSound := fun credential =>
  if h : credential = "Bearer tenant-1" then some ⟨⟨2⟩, by subst credential; simp [DemoAuthSound]⟩ else none

import Example.Tenant.Http
open Example.Tenant
example (result : Http.Outbound Handler.DemoAuthSound Handler.DemoAcquireSound "Bearer tenant-2") :
    Http.Outbound Handler.DemoAuthSound Handler.DemoAcquireSound "Bearer tenant-1" := result

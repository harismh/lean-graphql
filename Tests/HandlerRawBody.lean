import Example.Tenant.Http
open Example.Tenant
example := Http.respond (AuthSound := Handler.DemoAuthSound) (AcquireSound := Handler.DemoAcquireSound)
  (Protocol.Reply.mk .ok .json "SECRET".toUTF8)

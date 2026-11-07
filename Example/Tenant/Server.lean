import Example.Tenant.Http

namespace Example.Tenant.Server
open Std Async Handler

/-- Fault modes are local launch configuration for integration tests. -/
def run (args : List String) : IO Unit := Async.block do
  let port := (args.head?.bind String.toNat?).getD 8081
  if port == 0 || port > 65535 then throw (IO.userError "invalid port")
  let mode := args[1]?.getD "normal"
  let auth : Authenticate ContextAsync DemoAuthSound := fun credential => do
    if mode == "auth-throw" then throw (IO.userError "SECRET authentication details")
    demoAuthenticate credential
  let acquire : Acquire ContextAsync DemoAcquireSound := fun principal => do
    if mode == "snapshot-throw" then throw (IO.userError "SECRET snapshot details")
    if mode == "snapshot-none" then return none
    demoAcquire principal
  let backend : BackendFactory ContextAsync := fun context call pre => do
    if mode == "backend-throw" then throw (IO.userError "SECRET backend details")
    if mode == "transport" then return .error .unavailable
    demoBackend context call pre
  let router := Http.routes DemoAuthSound DemoAcquireSound auth acquire backend
  let address : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, UInt16.ofNat port⟩
  let server ← router.serve address
  IO.println s!"Certified tenant GraphQL: POST http://127.0.0.1:{port}/graphql"
  server.waitShutdown

end Example.Tenant.Server

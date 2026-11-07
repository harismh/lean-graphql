import Example.Resolvers
import GraphQL.LeanIO

open Std Async

def main (args : List String) : IO Unit := Async.block do
  let port := (args.head?.bind String.toNat?).getD 8080
  if port == 0 || port > 65535 then throw (IO.userError "port must be between 1 and 65535")
  let resolvers : Demo.Resolvers ContextAsync :=
    { demoResolvers with gql_Query := { queryResolvers with gql_broken := fun _ _ => throw (IO.userError "private backend details") } }
  let router := GraphQL.LeanIO.routes Demo.schema (Demo.dispatch resolvers)
  let address : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, UInt16.ofNat port⟩
  let server ← router.serve address
  IO.println s!"Lean GraphQL prototype: POST http://127.0.0.1:{port}/graphql"
  server.waitShutdown

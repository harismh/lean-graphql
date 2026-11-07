import Example.Schema
import GraphQL.Execution

open GraphQL

/-- Ordinary application code: generated argument types and result sums; no proofs. -/
def queryResolvers [Monad m] : Demo.Objects.Query m where
  gql_greeting _ _ := pure (.ok "Hello from Lean")
  gql_user _ args := pure (.ok (args.gql_id.toNat?.bind fun id =>
    if id == 1 || id == 2 then some ⟨id⟩ else none))
  gql_users _ _ := pure (.ok [⟨1⟩, ⟨2⟩])
  gql_optionalUsers _ _ := pure (.ok (some [⟨1⟩, ⟨2⟩]))
  gql_node _ _ := pure (.ok (.gql_User ⟨1⟩))
  gql_search _ _ := pure (.ok [.gql_User ⟨1⟩, .gql_Team ⟨10⟩])
  gql_broken _ _ := pure (.error "example resolver failure")
  gql_number _ args := pure (.ok (some args.gql_a))
  gql_optional _ args := pure (.ok (match args.gql_value with
    | .missing => "missing" | .null => "null" | .value v => v))
  gql_echo _ args := pure (.ok (match args.gql_filter with
    | .missing => "missing" | .null => "null"
    | .value (.mk query children) =>
      let text := match query with | .value s => s | .missing => "missing" | .null => "null"
      let count := match children with | .value xs => xs.length | _ => 0
      s!"{text}:{count}"))

def userResolvers [Monad m] : Demo.Objects.User m where
  gql_id ref _ := pure (.ok (toString ref.key))
  gql_name ref _ := pure (.ok (if ref.key == 1 then "Ada" else "Grace"))
  gql_friends ref _ := pure (.ok (if ref.key == 1 then [⟨2⟩] else [⟨1⟩]))
  gql_role ref _ := pure (.ok (if ref.key == 1 then .gql_ADMIN else .gql_MEMBER))
  gql_joined _ _ := pure (.ok "2026-11-01")
  gql_risky ref _ := pure (if ref.key == 2 then .error "user field failed" else .ok "ok")

def teamResolvers [Monad m] : Demo.Objects.Team m where
  gql_id ref _ := pure (.ok (toString ref.key))
  gql_label _ _ := pure (.ok "Research")

def demoResolvers [Monad m] : Demo.Resolvers m where
  gql_Query := queryResolvers
  gql_User := userResolvers
  gql_Team := teamResolvers

def demoQuery (query : String) (variables : Inputs := []) : Except String String := do
  let plan ← prepare Demo.schema query
  let machine ← execute plan variables
  return encodeCompletion (drive (m := Id) (Demo.dispatch demoResolvers) machine)

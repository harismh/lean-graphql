import Example.Resolvers

-- Expected to fail: String! cannot successfully return Option String.
def wrong : Demo.Resolvers Id :=
  { demoResolvers with gql_Query := { queryResolvers with gql_greeting := fun _ _ => .ok (none : Option String) } }

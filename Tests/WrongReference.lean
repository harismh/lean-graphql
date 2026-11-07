import Example.Schema

-- A real member constructor still requires its own object's reference type.
def wrong : Demo.Types.SearchResult := .gql_User (⟨0⟩ : GraphQL.Ref "Query")

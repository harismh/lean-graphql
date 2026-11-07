import Example.Schema

-- Expected to fail: Query is not a member of SearchResult.
def wrong : Demo.Types.SearchResult := .gql_Query ⟨0⟩

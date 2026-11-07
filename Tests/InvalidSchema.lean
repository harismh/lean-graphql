import GraphQL.Derive

-- Expected to fail before generating any declarations.
graphql_schema Invalid "type Query { unknown: Missing! }"

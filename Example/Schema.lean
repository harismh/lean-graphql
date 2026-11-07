import GraphQL.Derive

/- SDL is the source of the schema, enums, abstract sums, input types and resolver record.
    Keeping it in its own module gives Lake ordinary dependency tracking in this spike. -/
graphql_schema Demo r#"
scalar Date
enum Role { MEMBER ADMIN }
interface Node { id: ID! }
type User implements Node {
  id: ID!
  name: String!
  friends: [User!]!
  role: Role!
  joined: Date!
  risky: String!
}
type Team implements Node { id: ID! label: String! }
union SearchResult = User | Team
input Filter { query: String children: [Filter!] }
type Query {
  greeting: String!
  user(id: ID!): User
  users: [User!]!
  optionalUsers: [User!]
  node: Node!
  search: [SearchResult!]!
  broken: String
  number(a: Int!): Int
  optional(value: String): String!
  echo(filter: Filter): String!
}
"#

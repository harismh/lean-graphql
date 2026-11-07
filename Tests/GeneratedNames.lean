import GraphQL

-- Positive regressions: these schemas passed ValidCore but failed generation before review.
namespace Nested

graphql_schema Names "
  enum Option { A B }
  enum List { A }
  enum Except { A }
  enum Resolvers { A }
  enum schema { A }
  enum E { A }
  enum decodeE { B }
  enum GraphQL { A }
  enum Bool { A }
  enum Nat { A }
  enum Monad { A }
  type A_b { c: String! }
  type A { b_c: String! }
  type Query {
    one: Option
    many: [List!]!
    result(e: Except): String
    reserved: Resolvers
    metadata: schema
    encoded: E
    decoded: decodeE
    root: GraphQL
    bool: Bool
    nat: Nat
    effect: Monad
    a: A
    ab: A_b
  }
"

-- Same SDL field-name joining used to collide at A_b_c.
#check Names.Objects.A_b.gql_c
#check Names.Objects.A.gql_b_c
#check Names.Types.Option.gql_A

end Nested

graphql_schema EmptyInterface "
  interface Unused { id: ID! }
  type Query { a: String unused: Unused }
"

private def checkEmpty : IO Unit := do
  match GraphQL.prepare EmptyInterface.schema "{ unused { id } }" with
  | .ok _ => pure ()
  | .error e => throw (IO.userError e)
  match GraphQL.prepare EmptyInterface.schema "{ unused }" with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "empty interface was treated as a leaf")

#eval checkEmpty

graphql_schema RecursiveInputs "
  input Left { right: Right }
  input Right { left: Left }
  type Query { echo(value: Left): String }
"

graphql_schema Shapes "
  type C { value: String }
  type D { value: ID }
  type A { child: C }
  type B { child: D }
  union U = A | B
  type Query { u: U }
"

private def checkShapes : IO Unit := do
  match GraphQL.prepare Shapes.schema "{ u { ... on A { child { value } } ... on B { child { value } } } }" with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "nested SameResponseShape conflict was accepted")

#eval checkShapes

graphql_schema LeanInternals "enum E { rec mk } enum instBEqE { A } type rec { x: String } type Query { mk: String rec: E q(mk:String rec:String): rec }"

-- Lean's special _root_ declaration name and the escape prefix remain distinct.
graphql_schema RootEnum "enum _root_ { A } enum SDL__root_ { B } type Query { a: _root_ b: SDL__root_ }"
#check RootEnum.Types.SDL__root_.gql_A
#check RootEnum.Types.SDL_SDL__root_.gql_B

graphql_schema RootInput "input _root_ { nested: _root_ } input SDL__root_ { a: _root_ } type Query { a(x: SDL__root_): String }"

graphql_schema RootObject "type _root_ { value: String } type SDL__root_ { value: String } union U = _root_ | SDL__root_ type Query { a: U }"
#check RootObject.Objects.SDL__root_.gql_value
#check RootObject.Objects.SDL_SDL__root_.gql_value

graphql_schema RootInterface "interface _root_ { id: ID! } type User implements _root_ { id: ID! } type Query { node: _root_ }"

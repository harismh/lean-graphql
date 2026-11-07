import GraphQL.Syntax
import GraphQL.Plan.Arguments

namespace Example.Tenant.GenerationFixture

-- Deliberately reordered objects and colliding-looking names, recursive outputs,
-- same-typed arguments, nullable arguments, and three-component products.
abbrev ast : GraphQL.Schema := ⟨[
  ⟨"_root_", .object, [⟨"type", .named "String" true, []⟩,
    ⟨"next", .list (.named "_root_" true) false, []⟩], [], []⟩,
  ⟨"Query", .object, [⟨"lookup", .named "_root_" false,
    [⟨"left", .named "String" true⟩, ⟨"right", .named "String" true⟩,
     ⟨"limit", .named "Int" false⟩]⟩], [], []⟩], "Query"⟩

def sdl : String := "type _root_ { type: String! next: [_root_!] } type Query { lookup(left: String!, right: String!, limit: Int): _root_ }"

end Example.Tenant.GenerationFixture

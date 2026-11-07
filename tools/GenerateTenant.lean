import GraphQL.Plan.Generate
import Example.Tenant.Bindings
import Example.Tenant.GenerationFixture

open GraphQL.Plan.Generate

def config : Config where
  namespaceName := "Example.Tenant.Generated"
  imports := ["Example.Tenant.Bindings"]
  anchor := "Example.Tenant.Binding.demoAst"
  models := "Example.Tenant.Binding.carriers"
  scope := "Example.Tenant.Binding.Request"
  error := "Example.Tenant.ApplicationError"
  bindings := "Example.Tenant.Binding.independentBindings"

def main (args : List String) : IO Unit := do
  let some path := args[0]? | throw (IO.userError "output path required")
  let fixture := args[1]? == some "fixture"
  let input := if fixture then Example.Tenant.GenerationFixture.sdl else Example.Tenant.Binding.demoSDL
  let parsed ← match GraphQL.parseSchema input with
    | .ok ast => pure ast
    | .error message => throw (IO.userError message)
  let selected := if args[1]? == some "mutate" then { config with mutateSwap := some (1, 0, 1) } else config
  let selected := if fixture then { selected with
    namespaceName := "GeneratorFixture"
    imports := ["Example.Tenant.GenerationFixture"]
    anchor := "Example.Tenant.GenerationFixture.ast"
    models := "(fun _ => Unit)"
    scope := "Unit"
    error := "Unit"
    bindings := "(fun _ _ => ⟨(fun _ _ _ => .error (.application ())), none⟩)"
    } else selected
  let source ← match emit selected parsed with
    | .ok source => pure source
    | .error message => throw (IO.userError message)
  IO.FS.writeFile (System.FilePath.mk path) source

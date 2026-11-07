import Example.Tenant.Schema

#eval do
  match Example.Tenant.Binding.parsedDemo with
  | .error message => throw (IO.userError message)
  | .ok ast =>
    if ast = Example.Tenant.Binding.demoAst then
      IO.println "PASS tenant SDL parses to the independently checked readable AST"
    else throw (IO.userError "tenant SDL/readable AST mismatch")

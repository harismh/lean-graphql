import Example.Schema

-- Expected to fail: every object field needs a resolver.
def missing : Demo.Resolvers Id := {}

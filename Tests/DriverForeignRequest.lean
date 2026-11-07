import Example.Tenant.CertifiedExecution
open Example.Tenant Example.Tenant.Preparation Example.Tenant.CertifiedExecution
example (prepared : Prepared operation) (first second : Binding.Request) (supplied)
    (result : Result prepared first supplied) : Result prepared second supplied := result

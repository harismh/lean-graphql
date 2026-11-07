import GraphQL.Plan.CertifiedDriver
open GraphQL.Plan
example : CertifiedBackend Id (fun (_ : Unit) => True) (fun _ (answer : Bool) => answer = true) :=
  fun _ _ => ⟨false, by change false = true; decide⟩

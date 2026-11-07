import GraphQL.Plan.BoundedExample
open GraphQL.Plan
open GraphQL.Plan.BoundedExample
example : NodeProof contracts (.map (fun _ : Nat => 10) (Ref.here : Ref [Nat] Nat))
    (fun _ => True) (fun _ result => result ≤ 1) := .map (fun _ _ => by decide)

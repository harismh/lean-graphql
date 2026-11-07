import GraphQL.Plan.Schema

namespace GraphQL.Plan

/-- Pure pointwise meaning; an optimized batch backend must separately refine it. -/
def denoteCall (meanings : Meanings schema models scope app) :
    (call : Call schema models scope) → Answer app call
  | .one field context parent args => meanings field context parent args
  | .batch field context inputs => inputs.map (fun (parent, args) => meanings field context parent args)

theorem batch_position (meanings : Meanings schema models scope app)
    (field : FieldId schema object) (context : scope)
    (inputs : Vector (models object × field.Args) n) (i : Fin n) :
    (denoteCall meanings (.batch field context inputs)).get i =
      meanings field context (inputs.get i).1 (inputs.get i).2 := by
  simp [denoteCall, Vector.get, Fin.cast]

theorem call_contract (spec : Contracts schema models scope app)
    (meanings : Meanings schema models scope app)
    (correct : ∀ {object} (field : FieldId schema object) context parent args,
      spec.pre field context parent args →
        spec.post field context parent args (meanings field context parent args))
    (call : Call schema models scope) (pre : spec.Pre call) :
    spec.Post call (denoteCall meanings call) := by
  cases call with
  | one field context parent args => exact correct field context parent args pre
  | batch field context inputs =>
    intro i
    rw [batch_position]
    exact correct field context (inputs.get i).1 (inputs.get i).2 (pre.2 i)

end GraphQL.Plan

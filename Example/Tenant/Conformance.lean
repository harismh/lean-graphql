import Example.Tenant.Response

namespace Example.Tenant.Spec

mutual
  /-- Response shape only: no principal, snapshot, evaluator, or authorization rule. -/
  inductive ObjectConforms : ObjectType → PSelection → List (String × Value) → Prop
    | nil : ObjectConforms object .nil []
    | cons (declared : fieldShape object name = some shape)
        (head : ValueConforms shape children value)
        (tail : ObjectConforms object rest fields) :
        ObjectConforms object (.field name args children rest) ((name, value) :: fields)

  inductive ValueConforms : Shape → PSelection → Value → Prop
    | null (nullable : shape.nullable = true) : ValueConforms shape children .null
    | scalar : ValueConforms (.scalar n) .nil (.string value)
    | object (nested : ObjectConforms type children fields) :
        ValueConforms (.object type n) children (.object fields)
    | list (nested : ItemsConform type en children values) :
        ValueConforms (.list type n en) children (.array values)

  inductive ItemsConform : ObjectType → Bool → PSelection → List Value → Prop
    | nil : ItemsConform type en children []
    | cons (head : ValueConforms (.object type en) children value)
        (tail : ItemsConform type en children rest) :
        ItemsConform type en children (value :: rest)
end

def Conforms (selection : PSelection) (response : Response) : Prop :=
  ValidOperation selection ∧
    match response.data with
    | .object fields => ObjectConforms .query selection fields
    | .null => response.errors ≠ []
    | _ => False

theorem null_without_error_rejected (selection : PSelection) :
    ¬ Conforms selection ⟨.null, []⟩ := by
  intro h
  exact h.2 rfl

theorem conforming_names (h : ObjectConforms type selection fields) :
    fields.map Prod.fst = selection.names := by
  induction selection generalizing fields with
  | nil => cases h; rfl
  | field name args children rest _ ih =>
    cases h with
    | cons _ _ tail => simpa [PSelection.names] using congrArg (List.cons name) (ih tail)

end Example.Tenant.Spec

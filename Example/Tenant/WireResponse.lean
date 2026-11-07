import Example.Tenant.S6bProofs
import GraphQL.Plan.WireEncoding

namespace Example.Tenant.Wire
open GraphQL.Plan.WireEncoding

/- Independent correspondence between application values and ordered JSON values. -/
mutual
  inductive ValueMeaning : Spec.Value → GraphQL.ResponseValue → Prop where
    | null : ValueMeaning .null .null
    | string : ValueMeaning (.string text) (.string text)
    | array (items : ItemsMeaning source target) : ValueMeaning (.array source) (.array target)
    | object (fields : FieldsMeaning source target) : ValueMeaning (.object source) (.object target)
  inductive ItemsMeaning : List Spec.Value → List GraphQL.ResponseValue → Prop where
    | nil : ItemsMeaning [] []
    | cons (head : ValueMeaning source target) (tail : ItemsMeaning sources targets) : ItemsMeaning (source :: sources) (target :: targets)
  inductive FieldsMeaning : List (String × Spec.Value) → List (String × GraphQL.ResponseValue) → Prop where
    | nil : FieldsMeaning [] []
    | cons (head : ValueMeaning source target) (tail : FieldsMeaning sources targets) :
        FieldsMeaning ((name, source) :: sources) ((name, target) :: targets)
end

def value : Spec.Value → GraphQL.ResponseValue
  | .null => .null
  | .string text => .string text
  | .array items => .array (items.map value)
  | .object fields => .object (fields.map (fun field => (field.1, value field.2)))
termination_by source => sizeOf source
decreasing_by
  all_goals
    simp_wf
    have bound := List.sizeOf_lt_of_mem ‹_›
    first | omega | cases field; simp_all; omega

theorem value_correct (source : Spec.Value) : ValueMeaning source (value source) := by
  apply Spec.Value.rec
    (motive_1 := fun source => ValueMeaning source (value source))
    (motive_2 := fun fields => FieldsMeaning fields (fields.map (fun field => (field.1, value field.2))))
    (motive_3 := fun items => ItemsMeaning items (items.map value))
    (motive_4 := fun field => ValueMeaning field.2 (value field.2))
    (t := source)
  · rw [value]; exact .null
  · intro text; rw [value]; exact .string
  · intro fields valid; rw [value]; exact .object valid
  · intro items valid; rw [value]; exact .array valid
  · exact .nil
  · intro head tail hv ht; exact .cons hv ht
  · exact .nil
  · intro head tail hv ht; exact .cons hv ht
  · intro name source valid; exact valid

inductive Message : PublicError ApplicationError → String → Prop where
  | argument : Message (.framework .argument) "Invalid argument"
  | exhausted : Message (.framework .exhausted) "Resource limit exceeded"
  | internal : Message (.framework .internal) "Internal error"
  | unavailable : Message (.application .unavailable) "Unavailable"

def message : PublicError ApplicationError → String
  | .framework .argument => "Invalid argument"
  | .framework .exhausted => "Resource limit exceeded"
  | .framework .internal => "Internal error"
  | .application .unavailable => "Unavailable"

theorem message_correct (code : PublicError ApplicationError) : Message code (message code) := by
  cases code with
  | framework code => cases code <;> constructor
  | application code => cases code; constructor

inductive PathMeaning : Spec.Path → List GraphQL.ResponseValue → Prop where
  | nil : PathMeaning [] []
  | field (tail : PathMeaning source target) : PathMeaning (.field name :: source) (.string name :: target)
  | index (tail : PathMeaning source target) : PathMeaning (.index n :: source) (.int (Int.ofNat n) :: target)

def path (source : Spec.Path) : List GraphQL.ResponseValue := source.map (fun segment => match segment with
  | .field name => .string name | .index n => .int (Int.ofNat n))

theorem path_correct (source : Spec.Path) : PathMeaning source (path source) := by
  induction source with
  | nil => exact .nil
  | cons segment tail ih => cases segment <;> constructor <;> exact ih

inductive ErrorMeaning : Spec.Error → GraphQL.ResponseValue → Prop where
  | mk {source : Spec.Error} (meaning : Message source.code text) (position : PathMeaning source.path segments) :
      ErrorMeaning source (.object [("message", .string text), ("path", .array segments)])

inductive ErrorsMeaning : List Spec.Error → List GraphQL.ResponseValue → Prop where
  | nil : ErrorsMeaning [] []
  | cons (head : ErrorMeaning source target) (tail : ErrorsMeaning sources targets) :
      ErrorsMeaning (source :: sources) (target :: targets)

def error (source : Spec.Error) : GraphQL.ResponseValue :=
  .object [("message", .string (message source.code)), ("path", .array (path source.path))]

theorem errors_correct (sources : List Spec.Error) : ErrorsMeaning sources (sources.map error) := by
  induction sources with
  | nil => exact .nil
  | cons source tail ih => exact .cons (.mk (message_correct source.code) (path_correct source.path)) ih

inductive ResponseMeaning : Spec.Response → GraphQL.ResponseValue → Prop where
  | success (data : ValueMeaning source target) : ResponseMeaning ⟨source, []⟩ (.object [("data", target)])
  | errors (data : ValueMeaning source target) (nonempty : errors ≠ []) (valid : ErrorsMeaning errors encoded) :
      ResponseMeaning ⟨source, errors⟩ (.object [("data", target), ("errors", .array encoded)])

def response (source : Spec.Response) : GraphQL.ResponseValue :=
  if source.errors.isEmpty then .object [("data", value source.data)] else
    .object [("data", value source.data), ("errors", .array (source.errors.map error))]

theorem response_correct (source : Spec.Response) : ResponseMeaning source (response source) := by
  rcases source with ⟨data, errors⟩
  cases errors with
  | nil => exact .success (value_correct data)
  | cons head tail => exact .errors (value_correct data) (by simp) (errors_correct _)

def EncodesResponse (source : Spec.Response) (bytes : ByteArray) : Prop :=
  ∃ ordered, ResponseMeaning source ordered ∧ EncodesBytes ordered bytes

def encode (source : Spec.Response) : ByteArray := (response source).encode.toUTF8

theorem encode_correct (source : Spec.Response) : EncodesResponse source (encode source) :=
  ⟨_, response_correct source, encode_bytes_correct _⟩

def AuthorizedWireResponse (snapshot : Snapshot) (principal : Principal) (selection : PSelection) (bytes : ByteArray) : Prop :=
  ∃ structured, Spec.AuthorizedResponse snapshot principal selection structured ∧ EncodesResponse structured bytes

def encodeAuthorized (source : {response // Spec.AuthorizedResponse snapshot principal selection response}) :
    {bytes // AuthorizedWireResponse snapshot principal selection bytes} :=
  ⟨encode source.val, source.val, source.property, encode_correct source.val⟩

theorem bubble_encodes_root_null (errors : List Spec.Error) :
    EncodesResponse ⟨.null, errors⟩ (encode (Spec.envelope (.bubble errors))) := encode_correct _

end Example.Tenant.Wire

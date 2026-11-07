import GraphQL.Response

namespace GraphQL.Plan.WireEncoding
open WireScalar

/- Compact ordered JSON grammar. No constructor mentions the encoder. -/
mutual
  inductive EncodesOrderedJSON : ResponseValue → String → Prop where
    | null : EncodesOrderedJSON .null "null"
    | string (valid : Quoted value text) : EncodesOrderedJSON (.string value) text
    | int (valid : Integer value text) : EncodesOrderedJSON (.int value) text
    | true : EncodesOrderedJSON (.boolean true) "true"
    | false : EncodesOrderedJSON (.boolean false) "false"
    | array (valid : Elements values texts) :
        EncodesOrderedJSON (.array values) ("[" ++ String.intercalate "," texts ++ "]")
    | object (valid : Members fields texts) :
        EncodesOrderedJSON (.object fields) ("{" ++ String.intercalate "," texts ++ "}")
  inductive Elements : List ResponseValue → List String → Prop where
    | nil : Elements [] []
    | cons (head : EncodesOrderedJSON value text) (tail : Elements values texts) :
        Elements (value :: values) (text :: texts)
  inductive Members : List (String × ResponseValue) → List String → Prop where
    | nil : Members [] []
    | cons (key : Quoted name keyText) (value : EncodesOrderedJSON data valueText)
        (tail : Members fields texts) :
        Members ((name, data) :: fields) ((keyText ++ ":" ++ valueText) :: texts)
end

theorem encode_correct (value : ResponseValue) : EncodesOrderedJSON value value.encode := by
  apply ResponseValue.rec
    (motive_1 := fun value => EncodesOrderedJSON value value.encode)
    (motive_2 := fun values => Elements values (values.map ResponseValue.encode))
    (motive_3 := fun fields => Members fields (fields.map (fun (name, value) => jsonString name ++ ":" ++ value.encode)))
    (motive_4 := fun pair => EncodesOrderedJSON pair.2 pair.2.encode)
    (t := value)
  · rw [ResponseValue.encode]; exact .null
  · intro value; rw [ResponseValue.encode]; exact .string (quote_correct value)
  · intro value; rw [ResponseValue.encode]; exact .int (integer_correct value)
  · intro value; cases value <;> rw [ResponseValue.encode] <;> constructor
  · intro values valid; rw [ResponseValue.encode]; exact .array valid
  · intro fields valid; rw [ResponseValue.encode]; exact .object valid
  · exact .nil
  · intro head tail headValid tailValid; exact .cons headValid tailValid
  · exact .nil
  · intro head tail headValid tailValid; exact .cons (quote_correct head.1) headValid tailValid
  · intro name value valid; exact valid

/-- The bytes decode to a string in the independent ordered JSON grammar. -/
def EncodesBytes (value : ResponseValue) (bytes : ByteArray) : Prop :=
  ∃ text, EncodesOrderedJSON value text ∧ bytes.utf8Decode? = some text.toList.toArray

theorem encode_bytes_correct (value : ResponseValue) : EncodesBytes value value.encode.toUTF8 :=
  ⟨value.encode, encode_correct value, utf8_preserves value.encode⟩

theorem array_length (valid : Elements values texts) : texts.length = values.length := by
  induction values generalizing texts with
  | nil => cases valid; rfl
  | cons head tail ih => cases valid with
    | cons hv ht => simpa using congrArg Nat.succ (ih ht)

theorem object_length (valid : Members fields texts) : texts.length = fields.length := by
  induction fields generalizing texts with
  | nil => cases valid; rfl
  | cons head tail ih => cases valid with
    | cons key value ht => simpa using congrArg Nat.succ (ih ht)

end GraphQL.Plan.WireEncoding

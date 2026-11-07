import GraphQL.Plan.Arguments

namespace GraphQL.Plan.InputCoercion

inductive Scalar where
  | id | string | int | boolean
  deriving DecidableEq, Repr

def Scalar.denote : Scalar → Type
  | .id | .string => String
  | .int => Int
  | .boolean => Bool

structure ScalarType where
  scalar : Scalar
  required : Bool
  deriving DecidableEq, Repr

inductive Raw where
  | null | string (value : String) | int (value : Int) | boolean (value : Bool)
  | unsupported
  deriving DecidableEq, Repr

inductive Error where
  | required | scalar
  deriving DecidableEq, Repr

def intRange (value : Int) : Prop := -2147483648 ≤ value ∧ value ≤ 2147483647
instance (value : Int) : Decidable (intRange value) := inferInstanceAs (Decidable (_ ∧ _))

/-- Independent coercion relation; it does not mention the executable coercer. -/
inductive Meaning : (type : ScalarType) → Option Raw → Input type.scalar.denote → Prop where
  | omitted : Meaning ⟨scalar, false⟩ none .omitted
  | null : Meaning ⟨scalar, false⟩ (some .null) .null
  | idString : Meaning ⟨.id, required⟩ (some (.string value)) (.value value)
  | idInt : Meaning ⟨.id, required⟩ (some (.int value)) (.value (toString value))
  | string : Meaning ⟨.string, required⟩ (some (.string value)) (.value value)
  | int (range : intRange value) : Meaning ⟨.int, required⟩ (some (.int value)) (.value value)
  | boolean : Meaning ⟨.boolean, required⟩ (some (.boolean value)) (.value value)

def coerce (type : ScalarType) (raw : Option Raw) : Except Error (Input type.scalar.denote) :=
  match raw with
  | none => if type.required then .error .required else .ok .omitted
  | some .null => if type.required then .error .required else .ok .null
  | some value => match type.scalar, value with
    | .id, .string value => .ok (.value value)
    | .id, .int value => .ok (.value (toString value))
    | .string, .string value => .ok (.value value)
    | .int, .int value => if intRange value then .ok (.value value) else .error .scalar
    | .boolean, .boolean value => .ok (.value value)
    | _, _ => .error .scalar

theorem coerce_complete (meaning : Meaning type raw value) : coerce type raw = .ok value := by
  cases meaning <;> simp [coerce, *]

theorem coerce_sound (type : ScalarType) (raw : Option Raw) (value : Input type.scalar.denote)
    (success : coerce type raw = .ok value) : Meaning type raw value := by
  rcases type with ⟨scalar, required⟩
  cases raw with
  | none => cases required <;> simp [coerce] at success; subst value; exact .omitted
  | some raw =>
    cases raw with
    | null => cases required <;> simp [coerce] at success; subst value; exact .null
    | unsupported => cases scalar <;> simp [coerce] at success
    | string text =>
      cases scalar <;> simp [coerce] at success
      · subst value; exact .idString
      · subst value; exact .string
    | int number =>
      cases scalar <;> simp [coerce] at success
      · subst value; exact .idInt
      · split at success
        · have equal := Except.ok.inj success
          subst value; exact .int ‹_›
        · contradiction
    | boolean flag =>
      cases scalar <;> simp [coerce] at success
      subst value; exact .boolean

theorem meaning_unique (left : Meaning type raw a) (right : Meaning type raw b) : a = b :=
  Except.ok.inj ((coerce_complete left).symm.trans (coerce_complete right))

/-- Input defaults apply only to absence, including absence obtained from a variable. -/
def defaulted (fallback : Option Raw) (supplied : Option Raw) : Option Raw :=
  match supplied with | none => fallback | some value => some value

inductive DefaultMeaning : Option Raw → Option Raw → Option Raw → Prop where
  | missing : DefaultMeaning fallback none fallback
  | provided : DefaultMeaning fallback (some value) (some value)

theorem defaulted_sound (fallback supplied : Option Raw) : DefaultMeaning fallback supplied (defaulted fallback supplied) := by
  cases supplied <;> constructor

theorem defaulted_complete (proof : DefaultMeaning fallback supplied effective) : defaulted fallback supplied = effective := by
  cases proof <;> rfl

def encode : (scalar : Scalar) → Input scalar.denote → Option Raw
  | _, .omitted => none
  | _, .null => some .null
  | .id, .value value | .string, .value value => some (.string value)
  | .int, .value value => some (.int value)
  | .boolean, .value value => some (.boolean value)

/-- Literal/type validity is an inspectable syntax predicate, not checker success. -/
def LiteralValid (type : ScalarType) (raw : Raw) : Prop :=
  match raw with
  | .null => type.required = false
  | .string _ => type.scalar = .id ∨ type.scalar = .string
  | .int number => type.scalar = .id ∨ (type.scalar = .int ∧ intRange number)
  | .boolean _ => type.scalar = .boolean
  | .unsupported => False

instance (type : ScalarType) (raw : Raw) : Decidable (LiteralValid type raw) := by
  unfold LiteralValid; split <;> infer_instance

theorem literal_complete (valid : LiteralValid type raw) : ∃ value, Meaning type (some raw) value := by
  rcases type with ⟨scalar, required⟩
  cases raw with
  | null => simp [LiteralValid] at valid; subst required; exact ⟨.null, .null⟩
  | string value =>
    cases valid with
    | inl h => cases h; exact ⟨.value value, .idString⟩
    | inr h => cases h; exact ⟨.value value, .string⟩
  | int value =>
    cases valid with
    | inl h => cases h; exact ⟨.value (toString value), .idInt⟩
    | inr h => rcases h with ⟨h, range⟩; cases h; exact ⟨.value value, .int range⟩
  | boolean value => cases valid; exact ⟨.value value, .boolean⟩
  | unsupported => contradiction

theorem literal_sound (meaning : Meaning type (some raw) value) : LiteralValid type raw := by
  cases meaning <;> simp [LiteralValid, *]

/-- Public failure classification, independent of executable control flow. -/
def Rejected (type : ScalarType) (raw : Option Raw) (error : Error) : Prop :=
  match error, raw with
  | .required, none | .required, some .null => type.required = true
  | .scalar, some value => value ≠ .null ∧ ¬ LiteralValid type value
  | _, _ => False

theorem coerce_rejected (type : ScalarType) (raw : Option Raw) (error : Error) :
    coerce type raw = .error error ↔ Rejected type raw error := by
  rcases type with ⟨scalar, required⟩
  cases raw with
  | none => cases scalar <;> cases required <;> cases error <;> simp [coerce, Rejected]
  | some raw =>
    cases raw <;> cases scalar <;> cases required <;> cases error <;>
      simp [coerce, Rejected, LiteralValid] <;> split <;> simp_all

theorem required_value (meaning : Meaning ⟨scalar, true⟩ raw value) :
    ∃ result, value = .value result := by
  cases meaning <;> exact ⟨_, rfl⟩

theorem defaulted_none (raw : Option Raw) : defaulted none raw = raw := by
  cases raw <;> rfl

theorem default_null_preserved (fallback : Option Raw) : defaulted fallback (some .null) = some .null := rfl

/-- Deliberately incorrect defaulting, for a semantic mutation witness. -/
def nullDefaultMutation (fallback supplied : Option Raw) : Option Raw :=
  match supplied with | none | some .null => fallback | value => value

theorem null_default_mutation_rejected :
    ¬ (∀ fallback supplied effective, DefaultMeaning fallback supplied effective →
      nullDefaultMutation fallback supplied = effective) := by
  intro agreement
  have wrong := agreement (some (.string "fallback")) (some .null) (some .null) .provided
  cases wrong

end GraphQL.Plan.InputCoercion

import Std

namespace GraphQL.Plan.WireScalar

/-- Numeric character meanings, independent of the digit printer. -/
def Hex (n : Nat) (c : Char) : Prop := n < 16 ∧ c.toNat = if n < 10 then 48 + n else 87 + n
instance (n : Nat) (c : Char) : Decidable (Hex n c) := by unfold Hex; infer_instance

theorem hex_digit (n : Nat) (bound : n < 16) : Hex n (Nat.digitChar n) := by
  have table : ∀ i : Fin 16, Hex i.val (Nat.digitChar i.val) := by decide +kernel
  exact table ⟨n, bound⟩

inductive Escaped : Char → List Char → Prop where
  | raw (safe : 32 ≤ c.toNat) (quote : c ≠ '"') (slash : c ≠ '\\') : Escaped c [c]
  | quote : Escaped '"' ['\\', '"']
  | slash : Escaped '\\' ['\\', '\\']
  | control (bound : c.toNat < 32) (high : Hex h a) (low : Hex l b)
      (value : c.toNat = 16 * h + l) : Escaped c ['\\', 'u', '0', '0', a, b]

def escapeChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"'] else if c = '\\' then ['\\', '\\'] else
  if c.toNat < 32 then ['\\', 'u', '0', '0', Nat.digitChar (c.toNat / 16), Nat.digitChar (c.toNat % 16)] else [c]

theorem escape_char_correct (c : Char) : Escaped c (escapeChar c) := by
  unfold escapeChar
  split
  · rename_i equal; subst c; exact .quote
  · split
    · rename_i equal; subst c; exact .slash
    · split
      · rename_i quote slash bound
        exact .control bound (hex_digit _ (by omega)) (hex_digit _ (Nat.mod_lt _ (by decide)))
          (by omega)
      · rename_i quote slash safe
        exact .raw (by omega) quote slash

inductive Content : List Char → List Char → Prop where
  | nil : Content [] []
  | cons (head : Escaped c text) (tail : Content cs rest) : Content (c :: cs) (text ++ rest)

def quote (s : String) : String := String.ofList ('"' :: s.toList.flatMap escapeChar ++ ['"'])

def Quoted (s : String) (text : String) : Prop :=
  ∃ contents, Content s.toList contents ∧ text.toList = '"' :: contents ++ ['"']

theorem content_correct (chars : List Char) : Content chars (chars.flatMap escapeChar) := by
  induction chars with
  | nil => exact .nil
  | cons c cs ih => exact .cons (escape_char_correct c) ih

theorem quote_correct (s : String) : Quoted s (quote s) :=
  ⟨_, content_correct s.toList, by simp [quote]⟩

/-- Decimal syntax excludes leading zeroes by requiring a positive prefix. -/
inductive Decimal : Nat → List Char → Prop where
  | digit (bound : n < 10) (value : c.toNat = 48 + n) : Decimal n [c]
  | more (initial : Decimal n chars) (positive : 0 < n) (bound : d < 10)
      (value : c.toNat = 48 + d) : Decimal (n * 10 + d) (chars ++ [c])

def digits (n : Nat) : List Char :=
  if n < 10 then [Nat.digitChar n] else digits (n / 10) ++ [Nat.digitChar (n % 10)]
termination_by n

theorem digits_correct (n : Nat) : Decimal n (digits n) := by
  rw [digits]
  split
  · rename_i bound
    exact .digit bound (by simpa [Hex, bound] using (hex_digit n (by omega)).2)
  · rename_i large
    have divisor : n / 10 * 10 + n % 10 = n := by simpa [Nat.mul_comm] using Nat.div_add_mod n 10
    have recursive := digits_correct (n / 10)
    have digit := (hex_digit (n % 10) (by omega)).2
    have bound : n % 10 < 10 := Nat.mod_lt _ (by decide)
    simpa only [divisor] using Decimal.more recursive (by omega) bound (by simpa [bound] using digit)
termination_by n

def integer (n : Int) : String := match n with
  | .ofNat n => String.ofList (digits n)
  | .negSucc n => String.ofList ('-' :: digits (n + 1))

inductive Integer : Int → String → Prop where
  | nonnegative (valid : Decimal n chars) : Integer (.ofNat n) (String.ofList chars)
  | negative (valid : Decimal (n + 1) chars) : Integer (.negSucc n) (String.ofList ('-' :: chars))

theorem integer_correct (n : Int) : Integer n (integer n) := by
  cases n with
  | ofNat n => exact .nonnegative (digits_correct n)
  | negSucc n => exact .negative (digits_correct (n + 1))

/-- Independent UTF-8 decoder recovers exactly the emitted character sequence. -/
theorem utf8_preserves (text : String) : text.toUTF8.utf8Decode? = some text.toList.toArray := by
  obtain ⟨chars, rfl⟩ := text.exists_eq_ofList
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, String.toList_ofList]
  exact List.utf8Decode?_utf8Encode

end GraphQL.Plan.WireScalar

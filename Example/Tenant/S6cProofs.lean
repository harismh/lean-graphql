import Example.Tenant.WireResponse

namespace Example.Tenant.S6cProofs
open GraphQL GraphQL.Plan WireScalar WireEncoding

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

def tricky : String := "quote\" slash\\ newline\n tab\t 日本語 😀"
def controls : String := String.ofList ((List.range 32).map Char.ofNat)

theorem every_control_escaped : ∀ n : Fin 32,
    (escapeChar (Char.ofNat n.val)).length = 6 := by decide +kernel

theorem unicode_and_escapes : Quoted tricky (quote tricky) := quote_correct _
theorem controls_grammar : Quoted controls (quote controls) := quote_correct _
theorem supplementary_utf8 : tricky.toUTF8.utf8Decode? = some tricky.toList.toArray := utf8_preserves _
theorem numbers : integer 0 = "0" ∧ integer (-12345678901234567890) = "-12345678901234567890" := by decide +kernel

theorem raw_newline_rejected : ¬ Escaped '\n' ['\n'] := by
  intro bad
  cases bad with
  | raw safe _ _ => contradiction

theorem wrong_boolean_rejected : ¬ EncodesOrderedJSON (.boolean true) "false" := by
  intro bad
  have canonical : ∀ text, EncodesOrderedJSON (.boolean true) text → text = "true" := by
    intro text valid
    cases valid
    rfl
  have impossible := canonical _ bad
  contradiction

theorem shifted_path_rejected : ¬ Wire.PathMeaning [.field "projects", .index 0]
    [.string "projects", .int 1] := by
  intro bad
  cases bad with
  | field tail => cases tail

def failure : Spec.Response := ⟨.null, [⟨.framework .internal, [.field "projects", .index 0]⟩]⟩

theorem dropped_errors_rejected : ¬ Wire.ResponseMeaning failure (.object [("data", .null)]) := by
  intro bad
  cases bad

theorem root_bubble_wire : Wire.EncodesResponse failure (Wire.encode (Spec.envelope (.bubble failure.errors))) :=
  Wire.bubble_encodes_root_null _

theorem ordered_fields : (ResponseValue.object [("z", .int 1), ("a", .int 2)]).encode = "{\"z\":1,\"a\":2}" := by decide +kernel

def nativeTests : IO Unit := do
  for text in [tricky, controls, "", "é", "𐐀"] do
    let .ok (.str recovered) := Lean.Json.parse ((ResponseValue.string text).encode) |
      throw (IO.userError "S6c invalid encoded JSON string")
    unless recovered == text do throw (IO.userError "S6c string round-trip mismatch")
  for number in [0, 1, -1, 12345678901234567890, -12345678901234567890] do
    let .ok parsed := Lean.Json.parse ((ResponseValue.int number).encode) |
      throw (IO.userError "S6c invalid encoded JSON integer")
    unless parsed.getInt?.toOption == some number do throw (IO.userError "S6c integer round-trip mismatch")
  let expected := "{\"data\":null,\"errors\":[{\"message\":\"Internal error\",\"path\":[\"projects\",0]}]}"
  unless Wire.encode failure == expected.toUTF8 do throw (IO.userError "S6c envelope/path mismatch")
  IO.println "S6c: ordered JSON, escaping, integers, Unicode, errors and root-null encoding passed."

end Example.Tenant.S6cProofs

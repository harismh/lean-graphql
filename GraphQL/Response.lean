import Lean
import GraphQL.Plan.WireScalar

namespace GraphQL

inductive PathSegment where
  | field (name : String)
  | index (value : Nat)
  deriving Repr, BEq, DecidableEq

structure FieldError where
  message : String
  path : List PathSegment
  deriving Repr, BEq, DecidableEq

/-- Objects retain collected field order, unlike Lean.Json's tree-map objects. -/
inductive ResponseValue where
  | null
  | string (value : String)
  | int (value : Int)
  | boolean (value : Bool)
  | array (items : List ResponseValue)
  | object (fields : List (String × ResponseValue))
  deriving Repr, BEq, Inhabited

inductive Completion where
  | value (data : ResponseValue) (errors : List FieldError := [])
  | bubble (errors : List FieldError)
  deriving Repr, BEq

def Completion.errors : Completion → List FieldError
  | .value _ es | .bubble es => es

def nullableBoundary (required : Bool) (result : Completion) : Completion :=
  match required, result with
  | false, .bubble errors => .value .null errors
  | _, r => r

def collectItems : List Completion → Option (List ResponseValue) × List FieldError
  | [] => (some [], [])
  | .value v es :: rest =>
    let (values, errors) := collectItems rest
    (values.map (v :: ·), es ++ errors)
  | .bubble es :: rest => (none, es ++ (collectItems rest).2)

def completeList (required : Bool) (items : List Completion) : Completion :=
  let (values, errors) := collectItems items
  nullableBoundary required (match values with
    | some vs => .value (.array vs) errors
    | none => .bubble errors)

theorem nullableBoundary_stops (errors : List FieldError) :
    nullableBoundary false (.bubble errors) = .value .null errors := rfl

theorem nonNullBoundary_propagates (r : Completion) : nullableBoundary true r = r := by
  cases r <;> rfl

theorem collectItems_bubbles (items : List Completion) (errors : List FieldError)
    (h : Completion.bubble errors ∈ items) : (collectItems items).1 = none := by
  induction items with
  | nil => simp at h
  | cons head tail ih =>
    cases head with
    | bubble es => rfl
    | value v es =>
      simp only [List.mem_cons] at h
      have ht : Completion.bubble errors ∈ tail := by
        cases h with
        | inl h => cases h
        | inr h => exact h
      simp [collectItems, ih ht]

/-- A failed non-null list element propagates through a non-null list at any index. -/
theorem nonNullList_bubbles (items : List Completion) (errors : List FieldError)
    (h : Completion.bubble errors ∈ items) :
    completeList true items = .bubble (collectItems items).2 := by
  simp [completeList, collectItems_bubbles items errors h, nullableBoundary]

def jsonString (s : String) : String := Plan.WireScalar.quote s

/-- Total ordered encoder; correctness is proved in Plan.WireEncoding. -/
def ResponseValue.encode : ResponseValue → String
  | .null => "null"
  | .string s => jsonString s
  | .int i => Plan.WireScalar.integer i
  | .boolean b => if b then "true" else "false"
  | .array xs => "[" ++ String.intercalate "," (xs.map encode) ++ "]"
  | .object xs => "{" ++ String.intercalate "," (xs.map fun field => jsonString field.1 ++ ":" ++ encode field.2) ++ "}"

termination_by value => sizeOf value
decreasing_by
  all_goals
    simp_wf
    have bound := List.sizeOf_lt_of_mem ‹_›
    first
    | omega
    | cases field; simp_all; omega

def FieldError.toResponse (e : FieldError) : ResponseValue :=
  .object [("message", .string e.message), ("path", .array (e.path.map fun p =>
    match p with | .field n => .string n | .index i => .int i))]

def encodeCompletion (r : Completion) : String :=
  let data := match r with | .value v _ => v | .bubble _ => .null
  let fields := [("data", data)] ++
    (if r.errors.isEmpty then [] else [("errors", .array (r.errors.map (·.toResponse)))])
  ResponseValue.encode (.object fields)

def requestError (message : String) : String :=
  ResponseValue.encode (.object [("errors", .array [.object [("message", .string message)]])])

end GraphQL

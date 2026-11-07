import GraphQL.Syntax
import GraphQL.Machine

namespace GraphQL

/-- Prototype object carriers are typed references into application-owned storage. -/
structure Ref (typeName : String) where
  key : Nat
  deriving Repr, BEq, Inhabited

inductive RawValue where
  | null | string (s : String) | int (i : Int) | boolean (b : Bool)
  | enumValue (s : String) | object (typeName : String) (key : Nat)
  | list (items : List RawValue)
  deriving Repr, BEq, Inhabited

structure Call where
  owner : String
  parent : Nat
  field : Field
  arguments : List (String × InputValue)
  path : List PathSegment
  deriving Repr

abbrev Execution := Machine Call (fun _ => Except String RawValue)

def inputString : InputValue → Except String String
  | .string s => .ok s
  | _ => .error "expected String"

def inputID : InputValue → Except String String
  | .string s => .ok s
  | .int i => .ok (toString i)
  | _ => .error "expected ID"

def inputInt : InputValue → Except String Int32
  | .int i => if -2147483648 ≤ i && i ≤ 2147483647 then .ok (Int32.ofInt i)
    else .error "Int is outside the signed 32-bit range"
  | _ => .error "expected Int"

def inputBool : InputValue → Except String Bool
  | .boolean b => .ok b
  | _ => .error "expected Boolean"

def inputOptional (decode : InputValue → Except String α) : InputValue → Except String (Option α)
  | .null => .ok none
  | v => some <$> decode v

def inputList (decode : InputValue → Except String α) : InputValue → Except String (List α)
  | .list xs => xs.mapM decode
  | v => List.singleton <$> decode v

def requiredArgument (args : List (String × InputValue)) (name : String)
    (decode : InputValue → Except String α) : Except String α :=
  match args.lookup name with
  | none => .error s!"missing required argument '{name}'"
  | some value => decode value

def optionalArgument (args : List (String × InputValue)) (name : String)
    (decode : InputValue → Except String α) : Except String (Presence α) :=
  match args.lookup name with
  | none => .ok .missing
  | some .null => .ok .null
  | some value => Presence.value <$> decode value

end GraphQL

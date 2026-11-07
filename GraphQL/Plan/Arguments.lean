import GraphQL.Plan.SchemaEvidence

namespace GraphQL.Plan

/-- Names and original scalar type references stay in the layout. Unsupported input
kinds are rejected by CheckedIndexed, before this total representation is used. -/
def argumentKind (argument : GraphQL.Argument) : InputType := (inputEncoding argument.type).getD .unit

def argumentCode : List GraphQL.Argument → InputType
  | [] => .unit
  | [argument] => argumentKind argument
  | argument :: next :: rest => .pair (argumentKind argument) (argumentCode (next :: rest))

/-- Successful positional encoding agrees with the canonical argument record code. -/
theorem arguments_encoding_code (arguments : List GraphQL.Argument) (code : InputType)
    (encoded : argumentsEncoding arguments = some code) : code = argumentCode arguments := by
  match arguments with
  | [] => simpa [argumentsEncoding, argumentCode] using encoded.symm
  | [arg] =>
    simp only [argumentsEncoding] at encoded
    simp [argumentCode, argumentKind, encoded]
  | arg :: next :: rest =>
    cases head : inputEncoding arg.type with
    | none => simp [argumentsEncoding, head] at encoded
    | some first =>
      cases tail : argumentsEncoding (next :: rest) with
      | none => simp [argumentsEncoding, head, tail] at encoded
      | some remaining =>
        have eq : InputType.pair first remaining = code := by
          simpa [argumentsEncoding, head, tail] using encoded
        subst code
        simp [argumentCode, argumentKind, head, arguments_encoding_code (next :: rest) remaining tail]

inductive InputRef : InputType → InputType → Type where
  | here : InputRef kind kind
  | left (ref : InputRef left kind) : InputRef (.pair left right) kind
  | right (ref : InputRef right kind) : InputRef (.pair left right) kind

def InputRef.read : InputRef source target → source.denote → target.denote
  | .here, value => value
  | .left ref, value => ref.read value.1
  | .right ref, value => ref.read value.2

/-- The semantic projection is determined only by the independent AST coordinate. -/
def argumentRef : (arguments : List GraphQL.Argument) → (index : Fin arguments.length) →
    InputRef (argumentCode arguments) (argumentKind arguments[index])
  | [], index => nomatch index
  | [_], ⟨0, _⟩ => .here
  | [_], ⟨n + 1, bound⟩ => False.elim (by simp at bound <;> omega)
  | _ :: _ :: _, ⟨0, _⟩ => .left .here
  | _ :: next :: rest, ⟨n + 1, bound⟩ => .right (argumentRef (next :: rest) ⟨n, by simp_all <;> omega⟩)

/-- Canonical record identity is an AST argument coordinate, not emitted metadata. -/
abbrev ArgumentRecord (arguments : List GraphQL.Argument) :=
  (index : Fin arguments.length) → (argumentKind arguments[index]).denote

def packArguments (arguments : List GraphQL.Argument) (value : (argumentCode arguments).denote) : ArgumentRecord arguments :=
  fun index => (argumentRef arguments index).read value

def unpackArguments : (arguments : List GraphQL.Argument) → ArgumentRecord arguments → (argumentCode arguments).denote
  | [], _ => ()
  | [_], record => record ⟨0, by simp⟩
  | _ :: next :: rest, record => (record ⟨0, by simp⟩, unpackArguments (next :: rest) (fun index => record index.succ))

def ArgumentProjectionAgreement (arguments : List GraphQL.Argument)
    (pack : (argumentCode arguments).denote → ArgumentRecord arguments) : Prop :=
  ∀ value index, pack value index = (argumentRef arguments index).read value

theorem canonical_argument_projection (arguments : List GraphQL.Argument) :
    ArgumentProjectionAgreement arguments (packArguments arguments) := by intro _ _; rfl

theorem argument_projection_unique (arguments : List GraphQL.Argument)
    (pack : (argumentCode arguments).denote → ArgumentRecord arguments)
    (agreement : ArgumentProjectionAgreement arguments pack) : pack = packArguments arguments := by
  funext value index
  exact agreement value index

theorem unpack_pack_arguments (arguments : List GraphQL.Argument) (value : (argumentCode arguments).denote) :
    unpackArguments arguments (packArguments arguments value) = value := by
  match arguments with
  | [] => cases value; rfl
  | [_] => rfl
  | _ :: next :: rest =>
    exact congrArg (Prod.mk value.1) (unpack_pack_arguments (next :: rest) value.2)

theorem pack_unpack_arguments (arguments : List GraphQL.Argument) (record : ArgumentRecord arguments) :
    packArguments arguments (unpackArguments arguments record) = record := by
  funext index
  match arguments, index with
  | [], index => exact Fin.elim0 index
  | [_], ⟨0, _⟩ => rfl
  | [_], ⟨n + 1, bound⟩ => simp at bound <;> omega
  | _ :: _ :: _, ⟨0, _⟩ => rfl
  | _ :: next :: rest, ⟨n + 1, bound⟩ =>
    exact congrFun (pack_unpack_arguments (next :: rest) (fun index => record index.succ)) ⟨n, by simp_all <;> omega⟩

theorem checked_argument_layout (checked : CheckedIndexed ast) (owner : Fin ast.types.length)
    (field : CanonicalField ast owner) :
    ast.types[owner].fields[field].arguments = checked.indexed.argumentLayouts owner field.val :=
  (canonical_field_represents checked owner field).2.2.2

/-- A generated accessor is anchored to an actual name at an AST coordinate. -/
structure NamedArgument (arguments : List GraphQL.Argument) (name : String) where
  index : Fin arguments.length
  named : arguments[index].name = name

def NamedArgument.read (accessor : NamedArgument arguments name) (record : ArgumentRecord arguments) :
    (argumentKind arguments[accessor.index]).denote := record accessor.index

theorem named_argument_projection (accessor : NamedArgument arguments name)
    (value : (argumentCode arguments).denote) :
    accessor.read (packArguments arguments value) = (argumentRef arguments accessor.index).read value := rfl

end GraphQL.Plan

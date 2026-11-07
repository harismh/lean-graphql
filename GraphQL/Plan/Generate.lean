import GraphQL.Syntax
import GraphQL.Plan.Arguments
import GraphQL.Plan.Bindings

namespace GraphQL.Plan.Generate

/-- Application-supplied references remain outside the generated artifact. -/
structure Config where
  namespaceName : String
  imports : List String
  anchor : String
  models : String
  scope : String
  error : String
  bindings : String
  /-- Regression hook: changes dispatch AND its metadata, never the independent anchor. -/
  mutateSwap : Option (Nat × Nat × Nat) := none

def quote (value : String) : String := reprStr value
def list (values : List String) : String := "[" ++ String.intercalate ", " values ++ "]"

def typeSource : GraphQL.TypeRef → String
  | .named name required => s!"(.named {quote name} {required})"
  | .list item required => s!"(.list {typeSource item} {required})"

def argumentSource (argument : GraphQL.Argument) : String := s!"⟨{quote argument.name}, {typeSource argument.type}⟩"

def fieldSource (field : GraphQL.Field) : String :=
  s!"⟨{quote field.name}, {typeSource field.type}, {list (field.arguments.map argumentSource)}⟩"

def schemaSource (ast : GraphQL.Schema) : String :=
  "⟨" ++ list (ast.types.map (fun object =>
    s!"⟨{quote object.name}, .object, {list (object.fields.map fieldSource)}, [], []⟩")) ++ s!", {quote ast.query}⟩"

def inputSource : InputType → String
  | .unit => ".unit" | .string => ".string" | .int => ".int" | .boolean => ".boolean"
  | .optional inner => s!"(.optional {inputSource inner})"
  | .pair left right => s!"(.pair {inputSource left} {inputSource right})"

def outputSource : OutputType n → String
  | .string => ".string" | .int => ".int" | .boolean => ".boolean"
  | .object index => s!"(.object {index.val})"
  | .nullable inner => s!"(.nullable {outputSource inner})"
  | .list inner => s!"(.list {outputSource inner})"

def recordField (owner field : Nat) (objectName fieldName : String) : String :=
  s!"gql_{owner}_{field}_{objectName}_{fieldName}"

def selectedIndex (config : Config) (owner field : Nat) : Nat :=
  match config.mutateSwap with
  | some (object, left, right) => if owner = object then
      if field = left then right else if field = right then left else field
    else field
  | none => field

def casesPattern : Nat → String
  | 0 => "index"
  | count + 1 => "_ | (" ++ casesPattern count ++ ")"

/-- The generator is untrusted plumbing. Its artifacts must prove correspondence
against the supplied AST and binding family in the ordinary Lean kernel. -/
def emit (config : Config) (ast : GraphQL.Schema) : Except String String := do
  unless decide (WellFormedSchema ast) do throw "unsupported or invalid P1 schema"
  if ast.types.any (fun object => object.fields.isEmpty) then throw "P1 generation requires nonempty object field lists"
  let some root := objectIndex ast ast.query | throw "query root missing"
  let mut lines := config.imports.map (fun name => "import " ++ name)
  lines := lines ++ ["import GraphQL.Plan.Arguments", "import GraphQL.Plan.Bindings", "",
    "namespace " ++ config.namespaceName, "open GraphQL.Plan", "",
    "-- Generated artifact. Regenerate; do not edit the semantic anchor or implementations.",
    "set_option maxRecDepth 30000", "set_option maxHeartbeats 16000000", "",
    "abbrev ast : GraphQL.Schema := " ++ config.anchor,
    "def emittedAst : GraphQL.Schema := " ++ schemaSource ast,
    "theorem source_anchor : emittedAst = ast := by decide +kernel", ""]
  let mut cases : List String := []
  let mut layouts : List String := []
  let mut records : List String := []
  let mut values : List String := []
  let mut dispatch : List String := []
  let mut metadata : List String := []
  let mut argLines : List String := []
  let mut maxFields := 0
  for (object, owner) in ast.types.zipIdx do
    let mut fields : List String := []
    maxFields := max maxFields object.fields.length
    for (field, index) in object.fields.zipIdx do
      let some input := argumentsEncoding field.arguments | throw "unsupported arguments"
      let some output := outputEncoding ast field.type | throw "unsupported output"
      fields := fields ++ [s!"⟨{quote field.name}, {inputSource input}, {outputSource output}⟩"]
      layouts := layouts ++ [s!"  | {owner}, {index} => {list (field.arguments.map argumentSource)}"]
      let member := recordField owner index object.name field.name
      let identity := s!"(checked.field {owner} ⟨{index}, by decide⟩)"
      records := records ++ [s!"  {member} : FieldBinding {identity} {config.models} {config.scope} {config.error}"]
      values := values ++ [s!"bindings {owner} ⟨{index}, by decide⟩"]
      let chosenIndex := selectedIndex config owner index
      let some chosen := object.fields[chosenIndex]? | throw "mutation index outside object"
      let chosenMember := recordField owner chosenIndex object.name chosen.name
      let binding := if chosenIndex = index then s!"resolvers.{chosenMember}" else s!"⟨resolvers.{chosenMember}.single, none⟩"
      dispatch := dispatch ++ [s!"  | ⟨{owner}, _⟩, ⟨⟨{index}, _⟩⟩ => {binding}"]
      metadata := metadata ++ [s!"({owner}, {index}, {quote chosen.name})"]
      let argName := s!"Args_{owner}_{index}"
      let raw := s!"ast.types[{owner}].fields[{index}].arguments"
      argLines := argLines ++ [
        s!"abbrev {argName} := ArgumentRecord ({raw})",
        s!"def {argName}.pack (value : {identity}.Args) : {argName} := packArguments _ value",
        s!"def {argName}.unpack (record : {argName}) : {identity}.Args := unpackArguments _ record",
        s!"theorem {argName}_projection : ArgumentProjectionAgreement ({raw}) {argName}.pack := canonical_argument_projection _",
        s!"theorem {argName}_roundtrip (value : {identity}.Args) : {argName}.unpack ({argName}.pack value) = value  := unpack_pack_arguments ({raw}) value",
        s!"theorem {argName}_inverse (record : {argName}) : {argName}.pack ({argName}.unpack record) = record := pack_unpack_arguments ({raw}) record"]
      for (argument, argIndex) in field.arguments.zipIdx do
        argLines := argLines ++ [s!"def {argName}.arg_{argIndex}_{argument.name} : NamedArgument ({raw}) {quote argument.name} := ⟨⟨{argIndex}, by decide⟩, rfl⟩"]
    let pattern := if owner + 1 = ast.types.length then "_" else toString owner
    cases := cases ++ [s!"  | {pattern} => {list fields}"]
    dispatch := dispatch ++ [s!"  | ⟨{owner}, _⟩, ⟨⟨n + {object.fields.length}, h⟩⟩ => False.elim (by simp [indexed, ast] at h <;> omega)"]
  lines := lines ++ ["def indexed : IndexedSchema ast := ⟨(fun owner => match owner.val with",
    String.intercalate "\n" cases ++ s!"), {root.val}, (fun owner field => match owner.val, field with",
    String.intercalate "\n" layouts ++ "\n  | _, _ => [])⟩",
    "theorem well_formed : WellFormedSchema ast := by decide +kernel",
    "theorem represents : Represents ast indexed := by decide +kernel",
    "abbrev checked : CheckedIndexed ast := ⟨indexed, well_formed, represents⟩", "",
    String.intercalate "\n" argLines, "",
    "-- Internal plumbing: supported application input is BindingsByField via fromCanonical.",
    "structure Resolvers where", String.intercalate "\n" records, "",
    s!"def fromCanonical (bindings : BindingsByField checked {config.models} {config.scope} {config.error}) : Resolvers :=",
    "  ⟨" ++ String.intercalate ", " values ++ "⟩", "",
    s!"def adapter (resolvers : Resolvers) : Adapter indexed.schema {config.models} {config.scope} {config.error} :=",
    "  fun {owner} field => match owner, field with", String.intercalate "\n" dispatch,
    s!"  | ⟨n + {ast.types.length}, h⟩, _ => False.elim (by simp at h <;> omega)", "",
    "-- Descriptive only: no agreement theorem depends on this emitted metadata.",
    "def dispatchMetadata : List (Nat × Nat × String) := " ++ list metadata, "",
    s!"theorem adapter_agreement (bindings : BindingsByField checked {config.models} {config.scope} {config.error}) :",
    "    BindingAgreement bindings (adapter (fromCanonical bindings)) := by",
    "  intro owner field", "  rcases owner with ⟨owner, bound⟩", "  rcases field with ⟨field, valid⟩",
    "  rcases owner with " ++ casesPattern ast.types.length ++ " <;>",
    "    rcases field with " ++ casesPattern maxFields ++ " <;>",
    "    first | rfl | simp [ast] at bound valid <;> omega", "",
    "def application : Resolvers := fromCanonical " ++ config.bindings,
    "theorem application_agreement : BindingAgreement (checked := checked) " ++ config.bindings ++ " (adapter application) :=",
    "  adapter_agreement " ++ config.bindings, "", "end " ++ config.namespaceName]
  return String.intercalate "\n" lines ++ "\n"

end GraphQL.Plan.Generate

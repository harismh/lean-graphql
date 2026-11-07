import Harness.Common
import Harness.BenchmarkData

namespace Harness.Benchmark
open Harness

def measure (folder : System.FilePath) (label cmd : String) (args : Array String)
    (cwd : Option System.FilePath := none) (env : Array (String × Option String) := #[])
    (timeoutMs := 180000) : IO Lean.Json := do
  IO.println s!"Measuring {label}"
  let started ← IO.monoMsNow
  let result ← capture "/usr/bin/time" ((if System.Platform.isOSX then #["-l"] else #["-v"]) ++ #[cmd] ++ args) timeoutMs cwd env
  let elapsed := (← IO.monoMsNow) - started
  let log := folder / s!"{label}.log"
  IO.FS.writeFile log (result.stdout ++ result.stderr)
  let rss := (lines result.stderr).findSome? fun line =>
    if contains line.toLower "maximum resident set size" then
      if System.Platform.isOSX then (words line).head?.bind String.toNat?
      else ((words line).getLast?.bind String.toNat?).map (· * 1024)
    else none
  ensure (result.exitCode == 0) s!"Benchmark failed: {label}; see {log}"
  let some rss := rss | throw (IO.userError s!"Missing RSS measurement; see {log}")
  IO.println s!"{label}: {elapsed} ms, {rss} bytes RSS"
  return obj [("name", str label), ("milliseconds", num elapsed), ("max_rss_bytes", num rss),
    ("exit_code", num result.exitCode.toNat), ("log", str log.toString)]

def batch : IO Unit := do
  let output ← Harness.run ".lake/build/bin/graphql-tenant" #["--batch-benchmark"]
  let mut measurements := #[]
  for line in (lines output).filter (! ·.isEmpty) do
    let fields := line.splitOn ","
    ensure (fields.length == 6) s!"Unexpected native benchmark line: {line}"
    let mut values := []
    for (part, expected) in fields.zip ["capacity", "unique", "reference", "optimized", "whole_reference", "whole_optimized"] do
      let pair := part.splitOn "="
      ensure (pair.length == 2 && pair.head! == expected) "Unexpected native benchmark field"
      let some value := pair[1]!.toNat? | throw (IO.userError "Invalid native benchmark value")
      values := values ++ [value]
    let capacity := values[0]!; let unique := values[1]!; let optimized := values[3]!
    ensure (capacity > 0 && optimized == (unique + capacity - 1) / capacity && values[2]! == 5 && values[4]! == 12 && values[5]! == 7 + optimized)
      "Primitive-call count disagrees with the certified workload"
    measurements := measurements.push (obj ((["capacity", "distinct_keys", "reference_calls", "optimized_calls", "whole_reference_calls", "whole_optimized_calls"].zip values).map fun (k,v) => (k,num v)))
  ensure (measurements.size == 4) "Missing native benchmark cases"
  let report := obj [("scope", str "Native Machine-call counts, stage and whole program. No physical-request or latency claim."), ("measurements", .arr measurements)]
  IO.FS.createDirAll ".lake/benchmarks"
  IO.FS.writeFile ".lake/benchmarks/s4b.json" (report.pretty ++ "\n")
  IO.println report.pretty

def scalarTypes (objects fields : Nat) : List String := (List.range objects).map fun i =>
  let name := if i == 0 then "Query" else s!"T{i}"
  let fs := (List.range fields).map fun j => s!"⟨\"field{j}\", .named \"String\" true, []⟩"
  "⟨\"" ++ name ++ "\", .object, [" ++ String.intercalate ", " fs ++ "], [], []⟩"

def certificates (objects fields : Nat) : String :=
  BenchmarkData.header ++ "abbrev ast : GraphQL.Schema := ⟨[" ++ String.intercalate ",\n" (scalarTypes objects fields) ++ "], \"Query\"⟩\n" ++
  "def indexed : IndexedSchema ast := ⟨fun _ => [" ++ String.intercalate ", " ((List.range fields).map fun j => s!"⟨\"field{j}\", .unit, .string⟩") ++ "], 0, fun _ _ => []⟩\n" ++
  "theorem freshWellFormed : WellFormedSchema ast := by decide +kernel\ntheorem freshRepresents : Represents ast indexed := by decide +kernel\n#print axioms freshWellFormed\n#print axioms freshRepresents\n"

def partitionedSource (objects fields : Nat) (partitioned : Bool) : String := Id.run do
  let names := (List.range objects).map fun i => if i == 0 then "Query" else s!"T{i}"
  let mut raw := []; let mut typed := []
  for i in [:objects] do
    let target := (i+1) % objects
    let fs := (List.range fields).map fun j => "⟨\"f" ++ toString j ++ "\", .list (.named \"" ++ names[target]! ++ "\" true) true, [⟨\"left\", .named \"ID\" true⟩, ⟨\"right\", .named \"Int\" false⟩]⟩"
    raw := raw ++ ["⟨\"" ++ names[i]! ++ "\", .object, [" ++ String.intercalate ", " fs ++ "], [], []⟩"]
    typed := typed ++ ["| " ++ (if i+1 == objects then "_" else toString i) ++ " => [" ++ String.intercalate ", " ((List.range fields).map fun j => s!"⟨\"f{j}\", .pair .string (.optional .int), .list (.object {target})⟩") ++ "]"]
  let mut source := "import GraphQL.Plan.Arguments\nopen GraphQL.Plan\nset_option maxRecDepth 30000\nset_option maxHeartbeats 16000000\n" ++
    "abbrev ast : GraphQL.Schema := ⟨[" ++ String.intercalate ",\n" raw ++ "], \"Query\"⟩\n" ++
    "def indexed : IndexedSchema ast := ⟨(fun owner => match owner.val with\n" ++ String.intercalate "\n" typed ++ "), 0, fun _ _ => [⟨\"left\", .named \"ID\" true⟩, ⟨\"right\", .named \"Int\" false⟩]⟩\n" ++
    "theorem wellFormed : WellFormedSchema ast := by decide +kernel\n#print axioms wellFormed\n"
  if partitioned then
    for i in [:objects] do source := source ++ s!"theorem object{i} : ObjectRepresents ast indexed {i} := by decide +kernel\n#print axioms object{i}\n"
  else source := source ++ "theorem represents : Represents ast indexed := by decide +kernel\n#print axioms represents\n"
  return source ++ "theorem argsRoundtrip (value : (argumentCode [⟨\"left\", .named \"ID\" true⟩, ⟨\"right\", .named \"Int\" false⟩]).denote) : unpackArguments _ (packArguments _ value) = value := unpack_pack_arguments _ value\n#print axioms argsRoundtrip\n"

def save (folder : System.FilePath) (scope : String) (measurements : Array Lean.Json) : IO Unit := do
  IO.FS.writeFile (folder / "report.json") ((obj [("scope", str scope), ("toolchain", str (trim (← IO.FS.readFile "lean-toolchain"))), ("measurements", .arr measurements)]).pretty ++ "\n")

def schema (kind : String) (smoke : Bool) : IO Unit := do
  let folder : System.FilePath := s!".lake/benchmarks/{kind}"
  IO.FS.createDirAll folder
  let mut measurements := #[]
  if kind == "s2" then
    for (name, source) in [("small_tenant", BenchmarkData.small), ("mixed_profile", BenchmarkData.mixed),
        ("scalar_objects", certificates (if smoke then 3 else 300) 10)] do
      let file := folder / s!"{name}.lean"
      IO.FS.writeFile file source
      measurements := measurements.push (← measure folder name "scripts/lake" #["env", "lean", file.toString])
    save folder "Fresh kernel schema certificates; no generation or execution." measurements
  else
    for (objects, fields) in (if smoke then [(3, 2)] else [(12, 6), (80, 10)]) do
      for partitioned in [false, true] do
        for iteration in [:if smoke then 1 else 2] do
          let name := s!"objects{objects}_fields{fields}_perobject{partitioned}_run{iteration+1}"
          let file := folder / s!"{name}.lean"
          IO.FS.writeFile file (partitionedSource objects fields partitioned)
          measurements := measurements.push (← measure folder name "scripts/lake" #["env", "lean", file.toString])
    save folder "Fresh kernel certificates with ordered two-argument layouts and recursive outputs; per-object mode excludes composition." measurements

def prototype (smoke : Bool) : IO Unit := do
  let root ← IO.currentDir
  let folder := root / ".lake/benchmarks/prototype"
  let generated := folder / "generated"
  IO.FS.createDirAll (generated / "Bench")
  let objects := if smoke then 3 else 300
  let fields := 10
  let source := "import GraphQL.Schema\nopen GraphQL\nset_option maxRecDepth 20000\nset_option maxHeartbeats 8000000\n" ++
    "def largeSchema : Schema := ⟨[" ++ String.intercalate ",\n" (scalarTypes objects fields) ++ "], \"Query\"⟩\n" ++
    "def largeChecked : CheckedSchema := ⟨largeSchema, by decide +kernel⟩\n#print axioms largeChecked\n"
  IO.FS.writeFile (folder / "SchemaProof.lean") source
  let sdl := String.intercalate "\n" ((List.range objects).map fun i => "type " ++ (if i == 0 then "Query" else s!"T{i}") ++ " { " ++ String.intercalate " " ((List.range fields).map fun j => s!"field{j}: String!") ++ " }")
  IO.FS.writeFile (generated / "Bench/Schema.lean") ("import GraphQL\ngraphql_schema Large \"\n" ++ sdl ++ "\n\"\n#print axioms Large.schema\n")
  let resolver := "import Bench.Schema\ndef queryResolvers : Large.Objects.Query Id where\n" ++ String.intercalate "\n" ((List.range fields).map fun i => s!"  gql_field{i} _ _ := .ok \"before\"") ++ "\n"
  IO.FS.writeFile (generated / "Bench/Resolver.lean") resolver
  let lean := (System.FilePath.mk (trim (← lake #["env", "lean", "--print-prefix"]))) / "bin/lean"
  let leanPath := trim (← lake #["env", "printenv", "LEAN_PATH"])
  let environment := #[("LEAN_PATH", some (generated.toString ++ ":" ++ leanPath))]
  let mut measurements := #[]
  measurements := measurements.push (← measure folder "explicit_data" lean.toString #[(folder / "SchemaProof.lean").toString] none environment)
  measurements := measurements.push (← measure folder "generated_schema" lean.toString #["Bench/Schema.lean", "-o", "Bench/Schema.olean"] (some generated) environment)
  let artifact := generated / "Bench/Schema.olean"
  let before ← IO.FS.readBinFile artifact
  let modified := (← artifact.metadata).modified
  measurements := measurements.push (← measure folder "resolver_initial" lean.toString #["Bench/Resolver.lean", "-o", "Bench/Resolver.olean"] (some generated) environment)
  let parts := resolver.splitOn "\"before\""
  IO.FS.writeFile (generated / "Bench/Resolver.lean") (parts.head! ++ "\"after\"" ++ String.intercalate "\"before\"" parts.tail)
  measurements := measurements.push (← measure folder "resolver_incremental" lean.toString #["Bench/Resolver.lean", "-o", "Bench/Resolver.olean"] (some generated) environment)
  check "schema artifact reused" (before == (← IO.FS.readBinFile artifact) && modified == (← artifact.metadata).modified)
  save folder s!"Single runs: {objects} scalar object types, {objects*fields} fields; explicit evidence and real graphql_schema separately. Resolver workload implements ten Query fields. No performance guarantee." measurements

end Harness.Benchmark

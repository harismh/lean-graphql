import Harness.Generator

namespace Harness.Check
open Harness

def run : IO Unit := do
  IO.println "Building the project (output follows on completion; LEAN_GRAPHQL_TIMEOUT_SCALE increases process deadlines)."
  (← IO.getStdout).flush
  IO.print (← lake #["build"] 600000)
  Generator.run true true
  for executable in ["graphql-tests", "graphql-tenant"] do
    IO.print (← Harness.run s!".lake/build/bin/{executable}")
  for fixture in ["Tests/GeneratedNames.lean", "Tests/TenantSDL.lean"] do
    let result ← leanFile fixture
    ensure (result.exitCode == 0) (result.stdout ++ result.stderr)
    IO.print result.stdout
  let tenant ← sourceFiles "Example/Tenant"
  let proofs := (tenant ++ (← sourceFiles "GraphQL/Plan")).qsort (fun a b => a.toString < b.toString)
  Audit.selfTest
  let mut names : List String := []
  let mut imports := []
  for file in proofs do
    let discovered ← IO.ofExcept ((Audit.discover (← IO.FS.readFile file)).mapError (fun e => s!"{file}: {e}"))
    names := names ++ discovered
    imports := imports ++ ["import " ++ (file.withExtension "").toString.replace "/" "."]
  let generated : System.FilePath := ".lake/tenant-axiom-audit.lean"
  IO.FS.writeFile generated (String.intercalate "\n" imports ++ "\n" ++
    String.intercalate "\n" (names.map ("#print axioms " ++ ·)) ++ "\n")
  let mut auditCount := 0
  for file in [System.FilePath.mk "Tests/Axioms.lean", generated] do
    let expected := (lines (← IO.FS.readFile file)).filterMap fun line =>
      if line.startsWith "#print axioms " then some (trim (line.drop 14).toString) else none
    let result ← leanFile file 180000
    ensure (result.exitCode == 0) (result.stdout ++ result.stderr)
    Audit.verifyReports expected result.stdout
    IO.print result.stdout
    auditCount := auditCount + expected.length
  for file in tenant ++ (← sourceFiles "GraphQL") do
    ensure (Audit.sourceGuard (← IO.FS.readFile file)) s!"Disallowed proof/implementation escape hatch in {file}"
  for (name, needles) in FixtureData.rejections do
    let result ← leanFile s!"Tests/{name}.lean"
    let output := result.stdout ++ result.stderr
    ensure (result.exitCode != 0 && needles.all (fun needle => contains output.toLower needle.toLower))
      s!"Unexpected compile-failure result for {name}:\n{output}"
    IO.println s!"PASS compile rejection: {name}"
  IO.println s!"All build, semantic, proof-audit ({auditCount}), and compile-failure ({FixtureData.rejections.length}) checks passed."

end Harness.Check

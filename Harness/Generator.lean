import Harness.Audit
import Harness.FixtureData

namespace Harness.Generator
open Harness

def generate (path : String) (mode : Array String := #[]) : IO Unit := do
  discard <| lake (#["env", "lean", "--run", "tools/GenerateTenant.lean", path] ++ mode)

def run (verify : Bool) (mutation : Bool) : IO Unit := do
  let folder : System.FilePath := ".lake/generator-tests"
  IO.FS.createDirAll folder
  let original : System.FilePath := "Example/Tenant/Generated.lean"
  if verify then
    let fresh := folder / "Fresh.lean"
    generate fresh.toString
    check "generated SDL artifact reproduces exactly" ((← IO.FS.readBinFile fresh) == (← IO.FS.readBinFile original))
  else generate original.toString
  if mutation then
    let mutant := folder / "Mutated.lean"
    generate mutant.toString #["mutate"]
    let source ← IO.FS.readFile mutant
    ensure (contains source "| ⟨1, _⟩, ⟨⟨0, _⟩⟩ => ⟨resolvers.gql_1_1_Project_title.single, none⟩" &&
      contains source "(1, 0, \"title\")") "Mutation did not change actual dispatch and emitted metadata"
    let result ← leanFile mutant
    let output := result.stdout ++ result.stderr
    IO.FS.writeFile (folder / "mutation.log") output
    let first := (lines (← takeBefore source "theorem adapter_agreement")).length
    let last := (lines (← takeBefore source "def application")).length
    let mut failures : List Nat := []
    for line in lines output do
      if contains line "Mutated.lean:" && contains line ": error:" then
        let tail := (line.splitOn "Mutated.lean:")[1]!
        let some position := ((tail.splitOn ":").head!).toNat? | throw (IO.userError "Malformed mutation diagnostic")
        failures := failures ++ [position]
    check "generator mutation: swapped dispatch AND metadata rejected by independent agreement"
      (result.exitCode != 0 && !failures.isEmpty && failures.all (fun n => first ≤ n && n < last))
    let witness := folder / "MutationWitness.lean"
    let application ← fromMarker source "def application"
    let positiveSource := "import Example.Tenant.S2Proofs\n" ++ (← takeBefore source "theorem adapter_agreement") ++
      (← takeBefore application "theorem application_agreement") ++ FixtureData.mutationWitness ++
      (← fromMarker source "end Example.Tenant.Generated")
    IO.FS.writeFile witness positiveSource
    let positive ← leanFile witness
    IO.FS.writeFile (folder / "mutation-witness.log") (positive.stdout ++ positive.stderr)
    ensure (positive.exitCode == 0) (positive.stdout ++ positive.stderr)
    Audit.verifyReports ["Example.Tenant.Generated.mutation_disagrees"] positive.stdout
    check "positive mutation witness: actual generated adapter disagrees with independent application" true
  if verify then
    let fixture := folder / "Fixture.lean"
    generate fixture.toString #["fixture"]
    IO.FS.writeFile fixture ((← IO.FS.readFile fixture) ++ FixtureData.generatorFixture)
    let result ← leanFile fixture
    IO.FS.writeFile (folder / "fixture.log") (result.stdout ++ result.stderr)
    ensure (result.exitCode == 0) (result.stdout ++ result.stderr)
    check "generated reordered recursive schema, names, multiargument projections and omitted/null/value" true

end Harness.Generator

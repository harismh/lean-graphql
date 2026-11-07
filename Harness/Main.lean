import Harness.Check
import Harness.HttpTests
import Harness.Benchmark
import Harness.SelfTest

namespace Harness.Main

def main (args : List String) : IO Unit := do
  match args with
  | ["--http-client", port, wire] => Http.client (port.toNat?.getD 0) wire false
  | ["--disconnect", port, wire] => Http.client (port.toNat?.getD 0) wire true
  | ["--free-port"] => IO.println (← Http.freePort)
  | ["--self-test"] => SelfTest.run
  | ["--generate"] =>
    discard <| lake #["build", "GraphQL.Plan.Generate"]
    Generator.run false false
  | ["--generate", "--check"] =>
    discard <| lake #["build"] 600000
    Generator.run true true
  | ["--http-certified"] => Http.selfTest; HttpTests.certified
  | ["--http-legacy"] => Http.selfTest; HttpTests.legacy
  | ["--benchmark", "batch"] =>
    discard <| lake #["build"] 600000
    Benchmark.batch
  | ["--benchmark", "prototype"] =>
    discard <| lake #["build"] 600000
    Benchmark.prototype false
  | ["--benchmark", "prototype", "--smoke"] =>
    discard <| lake #["build"] 600000
    Benchmark.prototype true
  | ["--benchmark", kind] =>
    discard <| lake #["build"] 600000
    if kind == "s2" || kind == "s2b" then Benchmark.schema kind false else throw (IO.userError "Unknown benchmark")
  | ["--benchmark", kind, "--smoke"] =>
    discard <| lake #["build"] 600000
    if kind == "s2" || kind == "s2b" then Benchmark.schema kind true else throw (IO.userError "Unknown benchmark")
  | ["--all"] => SelfTest.run; Check.run; Http.selfTest; HttpTests.certified; HttpTests.legacy
  | [] => Check.run
  | _ => throw (IO.userError "Usage: scripts/check [--all|--http-certified|--http-legacy|--self-test|--generate [--check]]")

end Harness.Main

def main := Harness.Main.main

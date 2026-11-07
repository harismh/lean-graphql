import Harness.Audit
import Harness.Http

namespace Harness.SelfTest
open Harness

def run : IO Unit := do
  Audit.selfTest
  Http.selfTest
  let result ← capture "/bin/sh" #["-c", "printf stdout; printf stderr >&2; exit 7"] 5000
  check "process output and nonzero exit preserved" (result.exitCode == 7 && result.stdout == "stdout" && result.stderr == "stderr")
  for command in ["trap '' TERM; while :; do sleep 1; done", "sleep 20 & exit 0"] do
    let started ← IO.monoMsNow
    let timedOut ← try
      discard <| capture "/bin/sh" #["-c", command] 400 (scaleTimeout := false)
      pure false
    catch error => pure (contains error.toString "Timeout")
    check "process deadline and descendant-pipe cleanup" (timedOut && (← IO.monoMsNow) - started < 5000)

end Harness.SelfTest

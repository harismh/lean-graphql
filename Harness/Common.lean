import Lean
import Std.Async

namespace Harness

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def check (label : String) (condition : Bool) : IO Unit := do
  ensure condition label
  IO.println s!"PASS {label}"

def contains (text part : String) : Bool := (text.splitOn part).length > 1

def trim (text : String) : String := text.trimAscii.toString

def words (text : String) : List String :=
  ((text.toList.map (fun c => if c.isWhitespace then ' ' else c) |> String.ofList).splitOn " ").filter (! ·.isEmpty)

def lines (text : String) : List String := text.splitOn "\n"

def takeBefore (text marker : String) : IO String := do
  ensure (contains text marker) s!"Missing marker: {marker}"
  return (text.splitOn marker).head!

def fromMarker (text marker : String) : IO String := do
  ensure (contains text marker) s!"Missing marker: {marker}"
  return marker ++ String.intercalate marker (text.splitOn marker).tail

def stopChild {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO Unit := do
  if (← child.tryWait).isSome then return
  child.kill
  for _ in [:100] do
    if (← child.tryWait).isSome then return
    IO.sleep 10
  -- Only this unreaped child/process group is targeted; never a user server.
  discard <| IO.Process.output {cmd := "/bin/kill", args := #["-KILL", "--", s!"-{child.pid}"]}
  discard child.wait

/-- Drain both pipes concurrently; impose a deadline and always reap owned children. -/
def capture (cmd : String) (args : Array String := #[]) (timeoutMs : Nat := 180000)
    (cwd : Option System.FilePath := none) (env : Array (String × Option String) := #[])
    (scaleTimeout : Bool := true) : IO IO.Process.Output := do
  let timeoutMs ← if scaleTimeout then do
      let scale := (← IO.getEnv "LEAN_GRAPHQL_TIMEOUT_SCALE").getD "1"
      let some scale := scale.toNat? | throw (IO.userError "LEAN_GRAPHQL_TIMEOUT_SCALE must be a positive integer")
      ensure (scale > 0) "LEAN_GRAPHQL_TIMEOUT_SCALE must be a positive integer"
      pure (timeoutMs * scale)
    else pure timeoutMs
  let child ← IO.Process.spawn { cmd := cmd, args := args, cwd := cwd, env := env, setsid := true, stdin := .null, stdout := .piped, stderr := .piped }
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← IO.asTask child.stderr.readToEnd .dedicated
  let started ← IO.monoMsNow
  let exitCode ← IO.mkRef (none : Option UInt32)
  try
    repeat
      if (← exitCode.get).isNone then
        if let some code ← child.tryWait then exitCode.set (some code)
      if let some code ← exitCode.get then
        if (← IO.hasFinished stdout) && (← IO.hasFinished stderr) then
          return ⟨code, ← IO.ofExcept stdout.get, ← IO.ofExcept stderr.get⟩
      if (← IO.monoMsNow) - started > timeoutMs then
        throw (IO.userError s!"Timeout ({timeoutMs} ms): {cmd} {args}")
      IO.sleep 10
    throw (IO.userError "unreachable process loop")
  finally
    if (← exitCode.get).isNone then stopChild child
    else if !(← IO.hasFinished stdout) || !(← IO.hasFinished stderr) then
      -- A descendant in the owned process group can retain a pipe after the
      -- group leader exits. Do not block on Task.get beyond the deadline.
      discard <| IO.Process.output {cmd := "/bin/kill", args := #["-KILL", "--", s!"-{child.pid}"]}

def run (cmd : String) (args : Array String := #[]) (timeoutMs := 180000) : IO String := do
  let result ← capture cmd args timeoutMs
  ensure (result.exitCode == 0) s!"Command failed ({result.exitCode}): {cmd} {args}\n{result.stdout}{result.stderr}"
  return result.stdout

def lake (args : Array String) (timeoutMs := 180000) : IO String := run "scripts/lake" args timeoutMs

def leanFile (path : System.FilePath) (timeoutMs := 60000) : IO IO.Process.Output :=
  capture "scripts/lake" #["env", "lean", path.toString] timeoutMs

partial def sourceFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut result := #[]
  for entry in ← root.readDir do
    if ← entry.path.isDir then result := result ++ (← sourceFiles entry.path)
    else if entry.path.extension == some "lean" then result := result.push entry.path
  return result.qsort (fun a b => a.toString < b.toString)

def json (text : String) : IO Lean.Json := IO.ofExcept (Lean.Json.parse text)
def str (s : String) : Lean.Json := .str s
def num (n : Nat) : Lean.Json := Lean.toJson n
def obj (fields : List (String × Lean.Json)) : Lean.Json := Lean.Json.mkObj fields

def field (value : Lean.Json) (name : String) : IO Lean.Json := IO.ofExcept (value.getObjVal? name)
def string (value : Lean.Json) : IO String := IO.ofExcept value.getStr?
def nat (value : Lean.Json) : IO Nat := IO.ofExcept value.getNat?
def array (value : Lean.Json) : IO (Array Lean.Json) := IO.ofExcept value.getArr?
def index (value : Lean.Json) (index : Nat) : IO Lean.Json := do
  let values ← array value
  let some value := values[index]? | throw (IO.userError s!"Missing array position {index}")
  return value

end Harness

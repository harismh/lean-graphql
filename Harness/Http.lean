import Harness.Common
import Std.Async.TCP

namespace Harness.Http
open Harness Std Async

structure Response where
  status : Nat
  headers : List (String × String)
  body : String
  deriving Inhabited

def Response.header (r : Response) (name : String) : String :=
  ((r.headers.find? (fun p => p.1 == name.toLower)).map Prod.snd).getD ""

def boundary (bytes : ByteArray) (start : Nat) (separator : ByteArray) : Option Nat := Id.run do
  for i in [start:bytes.size] do
    if bytes.extract i (i + separator.size) == separator then return some i
  return none

def hex (text : String) : Except String Nat := do
  unless !text.isEmpty && text.toList.all Char.isHexDigit do throw "Invalid chunk size"
  return text.toList.foldl (fun n c => n * 16 + if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87) 0

def unchunk (bytes : ByteArray) : Except String ByteArray := do
  let mut position := 0
  let mut body := ByteArray.empty
  repeat
    let some ending := boundary bytes position "\r\n".toUTF8 | throw "Missing chunk header"
    let some line := String.fromUTF8? (bytes.extract position ending) | throw "Invalid chunk header encoding"
    let size ← hex ((line.splitOn ";").head!)
    position := ending + 2
    if size == 0 then
      unless bytes.extract position bytes.size == "\r\n".toUTF8 do throw "Unexpected chunk trailer"
      return body
    unless position + size + 2 ≤ bytes.size && bytes.extract (position + size) (position + size + 2) == "\r\n".toUTF8 do
      throw "Truncated chunk"
    body := body ++ bytes.extract position (position + size)
    position := position + size + 2
  throw "Missing final chunk"

def parse (bytes : ByteArray) : Except String Response := do
  let some ending := boundary bytes 0 "\r\n\r\n".toUTF8 | throw "Missing HTTP headers"
  let some headText := String.fromUTF8? (bytes.extract 0 ending) | throw "Invalid HTTP headers"
  let headLines := headText.splitOn "\r\n"
  let statusLine := words headLines.head!
  unless statusLine.head! == "HTTP/1.1" || statusLine.head! == "HTTP/1.0" do throw "Invalid HTTP version"
  let some status := statusLine[1]?.bind String.toNat? | throw "Invalid HTTP status"
  unless 100 ≤ status && status ≤ 599 do throw "Invalid HTTP status range"
  let mut headers := []
  for line in headLines.tail do
    let parts := line.splitOn ":"
    unless parts.length ≥ 2 do throw "Malformed HTTP header"
    let name := trim parts.head! |>.toLower
    unless !name.isEmpty && !(headers.any (fun p => p.1 == name)) do throw "Empty or duplicate HTTP header"
    headers := headers ++ [(name, trim (String.intercalate ":" parts.tail))]
  let raw := bytes.extract (ending + 4) bytes.size
  let lookup (name : String) := ((headers.find? (fun p => p.1 == name)).map Prod.snd).getD ""
  let body ← if lookup "transfer-encoding" == "chunked" then
      if lookup "content-length" != "" then throw "Conflicting HTTP framing" else unchunk raw
    else do
      unless lookup "transfer-encoding" == "" do throw "Unsupported HTTP framing"
      let some size := (lookup "content-length").toNat? | throw "Missing content length"
      unless size == raw.size do throw "Content length mismatch"
      pure raw
  let some text := String.fromUTF8? body | throw "Invalid UTF-8 response"
  return ⟨status, headers, text⟩

def encodeResponse (r : Response) : Lean.Json := obj [
  ("status", num r.status), ("headers", obj (r.headers.map fun p => (p.1, str p.2))), ("body", str r.body)]

def decodeResponse (j : Lean.Json) : IO Response := do
  let headers ← field j "headers"
  let pairs ← IO.ofExcept headers.getObj?
  return ⟨← nat (← field j "status"), pairs.toArray.toList.map (fun p => (p.1, p.2.getStr?.toOption.getD "")),
    ← string (← field j "body")⟩

def address (port : Nat) : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩

/-- Separate client process: the parent owns the deadline and can close all sockets
by terminating it. No server parser or GraphQL implementation is used here. -/
def client (port : Nat) (wire : String) (disconnect : Bool) : IO Unit := Async.block do
  let socket ← TCP.Socket.Client.mk
  socket.connect (address port)
  socket.send wire.toUTF8
  if disconnect then return
  let mut bytes := ByteArray.empty
  repeat
    let some chunk ← socket.recv? 65536 | break
    bytes := bytes ++ chunk
    if bytes.size > 2097152 then throw (IO.userError "HTTP test response exceeds 2 MiB")
  let response ← IO.ofExcept (parse bytes)
  IO.println (encodeResponse response).compress

def freePort : IO Nat := do
  let socket ← TCP.Socket.Server.mk
  socket.bind (address 0)
  return (← socket.getSockName).port.toNat

structure Request where
  body : String := ""
  method : String := "POST"
  content : String := "application/json"
  accept : String := "application/graphql-response+json"
  auth : String := "Bearer tenant-1"

def request (port : Nat) (r : Request := {}) : IO Response := do
  let wire := s!"{r.method} /graphql HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\nContent-Type: {r.content}\r\nAccept: {r.accept}\r\nAuthorization: {r.auth}\r\nContent-Length: {r.body.utf8ByteSize}\r\n\r\n{r.body}"
  let result ← Harness.run (← IO.appPath).toString #["--http-client", toString port, wire] 10000
  decodeResponse (← json result)

def query (text : String) (fields : List (String × Lean.Json) := []) : Request :=
  {body := (obj (("query", str text) :: fields)).compress}

def Response.json (r : Response) : IO Lean.Json := Harness.json r.body

def withServer (binary mode : String) (action : Nat → IO Unit) : IO Unit := do
  let portText ← Harness.run (← IO.appPath).toString #["--free-port"] 5000
  let some port := (trim portText).toNat? | throw (IO.userError "Invalid allocated port")
  let child ← IO.Process.spawn {cmd := s!".lake/build/bin/{binary}", args := #[toString port, mode], setsid := true, stdin := .null, stdout := .piped, stderr := .piped}
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← IO.asTask child.stderr.readToEnd .dedicated
  let reaped ← IO.mkRef false
  try
    let started ← IO.monoMsNow
    let mut ready := false
    while !ready do
      if let some code ← child.tryWait then
        reaped.set true
        throw (IO.userError s!"HTTP test server exited before readiness ({code})")
      ensure ((← IO.monoMsNow) - started < 15000) "HTTP test server readiness timeout"
      ready ← try
        let result ← request port {method := "GET"}
        pure (result.status == 405)
      catch _ => pure false
      if !ready then IO.sleep 50
    action port
  finally
    unless ← reaped.get do stopChild child
    IO.FS.writeFile s!".lake/{binary}-{mode}-http.log" ((← IO.ofExcept stdout.get) ++ (← IO.ofExcept stderr.get))

def selfTest : IO Unit := do
  let good := "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\n{}"
  ensure ((parse good.toUTF8).toOption.map (·.body) == some "{}") "HTTP framing self-test"
  let chunked := "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\n{}\r\n0\r\n\r\n"
  ensure ((parse chunked.toUTF8).toOption.map (·.body) == some "{}") "HTTP chunk self-test"
  for bad in [good.replace "Length: 2" "Length: 3", good.replace "200" "BAD",
      chunked.replace "2\r\n{}" "5\r\n{}", good.replace "Content-Length: 2" "Content-Length: 2\r\nContent-Length: 2"] do
    ensure ((parse bad.toUTF8).toOption.isNone) "HTTP client accepted malformed framing"
  check "HTTP framing self-tests" true

end Harness.Http

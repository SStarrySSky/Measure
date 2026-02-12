/-
Copyright (c) 2026 Measure Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

TCP/stdio transport layer for engine communication (IO monad).
See ARCHITECTURE.md Section 8.1.
-/
import Measure.External.Protocol
import Measure.External.Messages

namespace Measure.External

/-- Connection handle for an active transport. -/
structure ConnectionHandle where
  id        : Nat
  transport : Transport
  isOpen    : Bool := true
  deriving Repr, Inhabited

/-- Transport-layer errors. -/
inductive TransportError where
  | connectionRefused (host : String) (port : Nat)
  | connectionClosed
  | timeout (ms : Nat)
  | ioError (msg : String)
  | parseError (msg : String)
  deriving Repr, Inhabited

/-- Result type for transport operations. -/
abbrev TransportResult (α : Type) := Except TransportError α

namespace TransportIO

/-- Open a TCP connection to an engine adapter. -/
def connectTcp (host : String) (port : Nat) : IO (TransportResult ConnectionHandle) := do
  -- Skeleton: real implementation would use Socket API
  IO.println s!"[Transport] Connecting to {host}:{port}..."
  return .ok { id := 0, transport := .tcp host port }

/-- Open a stdio connection by spawning a child process. -/
def connectStdio (command : String) : IO (TransportResult ConnectionHandle) := do
  IO.println s!"[Transport] Spawning: {command}"
  return .ok { id := 0, transport := .stdio command }

/-- Open a connection based on Transport config. -/
def connect (t : Transport) : IO (TransportResult ConnectionHandle) :=
  match t with
  | .tcp host port  => connectTcp host port
  | .stdio command  => connectStdio command
  | .unixSocket _path =>
    return .error (.ioError "Unix sockets not supported on this platform")

/-- Send a JSON-RPC request over the connection. -/
def sendRequest (_conn : ConnectionHandle) (req : ComputeRequest)
    : IO (TransportResult Unit) := do
  IO.println s!"[Transport] Sending request id={req.id} method={req.method.toRpcMethod}"
  return .ok ()

/-- Receive a JSON-RPC response from the connection. -/
def receiveResponse (_conn : ConnectionHandle)
    : IO (TransportResult ComputeResponse) := do
  -- Skeleton: real implementation would read from socket/pipe and parse JSON
  return .error (.timeout 30000)

/-- Close the connection. -/
def close (conn : ConnectionHandle) : IO ConnectionHandle := do
  IO.println s!"[Transport] Closing connection id={conn.id}"
  return { conn with isOpen := false }

/-- Send request and wait for response (synchronous round-trip). -/
def roundTrip (conn : ConnectionHandle) (req : ComputeRequest)
    : IO (TransportResult ComputeResponse) := do
  match ← sendRequest conn req with
  | .error e => return .error e
  | .ok () => receiveResponse conn

end TransportIO

end Measure.External

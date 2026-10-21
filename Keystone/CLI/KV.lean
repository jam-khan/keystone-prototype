import Keystone.KV.Controller
import Keystone.CLI.Json

open Lean Keystone.KV
namespace KVCommand

def leaseJson (lease : Lease) : Json := Json.mkObj [
  ("page", toJson lease.page), ("owner", toJson lease.owner),
  ("generation", toJson lease.generation)]

def ticketJson (ticket : Ticket) : Json := Json.mkObj [
  ("id", toJson ticket.id), ("owner", toJson ticket.owner),
  ("pages", toJson (ticket.pages.map leaseJson))]

def stateJson (s : State) : Json := Json.mkObj [
  ("capacity", toJson s.capacity), ("allocations", toJson (s.allocations.map leaseJson)),
  ("pending", toJson (s.pending.map ticketJson)), ("retired", toJson s.retired),
  ("next_generation", toJson s.nextGeneration), ("next_ticket", toJson s.nextTicket)]

private def parseLease (json : Json) : Except String Lease := do
  Keystone.CLI.object json ["page", "owner", "generation"]
  return ⟨← Keystone.CLI.nat json "page", ← Keystone.CLI.nat json "owner",
           ← Keystone.CLI.nat json "generation"⟩

private def action (s : State) (json : Json) : Except String (State × Json) := do
  match ← Keystone.CLI.string json "op" with
  | "allocate" =>
    Keystone.CLI.object json ["op", "owner"]
    match allocate s (← Keystone.CLI.nat json "owner") with
    | none => return (s, Json.mkObj [("accepted", toJson false)])
    | some (next, lease) => return (next, Json.mkObj [
        ("accepted", toJson true), ("lease", leaseJson lease)])
  | "submit" =>
    Keystone.CLI.object json ["op", "owner", "pages"]
    let pages ← (← Keystone.CLI.array json "pages").toList.mapM parseLease
    match submit s (← Keystone.CLI.nat json "owner") pages with
    | none => return (s, Json.mkObj [("accepted", toJson false)])
    | some (next, ticket) => return (next, Json.mkObj [
        ("accepted", toJson true), ("ticket", ticketJson ticket)])
  | "retire" =>
    Keystone.CLI.object json ["op", "owner"]
    return (retire s (← Keystone.CLI.nat json "owner"),
            Json.mkObj [("accepted", toJson true)])
  | "complete" =>
    Keystone.CLI.object json ["op", "ticket"]
    let id ← Keystone.CLI.nat json "ticket"
    let known := s.pending.any (fun ticket => ticket.id == id)
    return (complete s id, Json.mkObj [("accepted", toJson known)])
  | _ => throw "unknown controller operation"

def handle (json : Json) : Except String Json := do
  Keystone.CLI.object json ["capacity", "actions"]
  let capacity ← Keystone.CLI.nat json "capacity"
  let actions ← Keystone.CLI.array json "actions"
  if capacity > 4096 ∨ actions.size > 4096 then throw "controller runner limit exceeded"
  let mut s := init capacity
  let mut trace : Array Json := #[]
  for operation in actions do
    let (next, result) ← action s operation
    s := next
    trace := trace.push (Json.mkObj [
      ("operation", operation), ("result", result), ("state", stateJson s)])
  return Json.mkObj [("status", toJson "ok"), ("trace", toJson trace),
                     ("state", stateJson s)]

end KVCommand

def main : IO UInt32 := Keystone.CLI.serve KVCommand.handle

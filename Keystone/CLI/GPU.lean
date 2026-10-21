import Keystone.GPU.Model
import Keystone.CLI.Json

open Lean Keystone.GPU
namespace GPUCommand

private def spaceName : Space → String
  | .pageTable => "page_table"
  | .cache => "cache"
  | .output => "output"

private def accessJson (a : Access) : Json := Json.mkObj [
  ("lane", toJson a.lane), ("space", toJson (spaceName a.space)),
  ("address", toJson a.address)]

private def faultJson : Fault → Json
  | .invalidLane lane => Json.mkObj [("kind", toJson "invalid_lane"), ("lane", toJson lane)]
  | .outOfBounds access => Json.mkObj [
      ("kind", toJson "out_of_bounds"), ("access", accessJson access)]

private def word (json : Json) : Except String UInt32 := do
  let value ← json.getNat?
  if value ≥ 2^32 then throw "cache values must be uint32"
  return UInt32.ofNat value

def handle (json : Json) : Except String Json := do
  Keystone.CLI.object json ["page_size", "tokens", "block_size", "table", "cache"]
    ["schedule"]
  let pageSize ← Keystone.CLI.nat json "page_size"
  let n ← Keystone.CLI.nat json "tokens"
  let blockSize ← Keystone.CLI.nat json "block_size"
  if blockSize = 0 ∨ pageSize = 0 then throw "block_size and page_size must be positive"
  let lanes := ((n + blockSize - 1) / blockSize) * blockSize
  let table ← Keystone.CLI.array json "table"
  let cache ← Keystone.CLI.array json "cache"
  -- These limits protect the executable interpreter, not the general theorems.
  if lanes > 4096 ∨ table.size > 4096 ∨ cache.size > 65536 then
    throw "model runner limit exceeded (4096 lanes/table entries, 65536 cache words)"
  let cfg : Config := ⟨n, pageSize, lanes⟩
  let input : Input := ⟨← table.mapM Json.getNat?, ← cache.mapM word⟩
  unless validateInput cfg input do throw "invalid gather contract (coverage or physical-page bounds)"
  let schedule ← match Keystone.CLI.optional json "schedule" with
    | none => pure (roundRobin cfg)
    | some value => do
      let entries ← value.getArr?
      if entries.size > 32768 then throw "schedule exceeds model runner limit (32768 steps)"
      pure (← entries.toList.mapM Json.getNat?)
  let common := [("lanes", toJson lanes), ("steps", toJson schedule.length),
    ("reference", toJson ((reference cfg input).map UInt32.toNat))]
  match run cfg input schedule init with
  | .error fault => return Json.mkObj (common ++ [
      ("status", toJson "fault"), ("fault", faultJson fault)])
  | .ok (machine, accesses) => return Json.mkObj (common ++ [
      ("status", toJson (if completed cfg machine then "completed" else "incomplete")),
      ("output", toJson ((outputValues cfg machine).map (Option.map UInt32.toNat))),
      ("accesses", toJson (accesses.map accessJson))])

end GPUCommand

def main : IO UInt32 := Keystone.CLI.serve GPUCommand.handle

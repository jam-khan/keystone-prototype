import Keystone.GPU.KVGather
import Keystone.CLI.Json

open Lean Keystone.GPU
namespace GPUCommand

private def bufferName : Buffer → String
  | .pageTable => "page_table"
  | .kvCache => "kv_cache"
  | .output => "output"

private def accessJson (a : Access) : Json := Json.mkObj [
  ("thread", toJson a.thread), ("buffer", toJson (bufferName a.buffer)),
  ("index", toJson a.index)]

private def faultJson : Fault → Json
  | .invalidThread tid => Json.mkObj [("kind", toJson "invalid_thread"), ("thread", toJson tid)]
  | .outOfBounds access => Json.mkObj [
      ("kind", toJson "out_of_bounds"), ("access", accessJson access)]

private def word (json : Json) : Except String UInt32 := do
  let value ← json.getNat?
  if value ≥ 2^32 then throw "KV-cache entries must be uint32"
  return UInt32.ofNat value

def handle (json : Json) : Except String Json := do
  Keystone.CLI.object json ["page_size", "num_tokens", "block_size", "page_table", "kv_cache"]
    ["schedule"]
  let pageSize ← Keystone.CLI.nat json "page_size"
  let numTokens ← Keystone.CLI.nat json "num_tokens"
  let blockSize ← Keystone.CLI.nat json "block_size"
  if blockSize = 0 ∨ pageSize = 0 then throw "block_size and page_size must be positive"
  let numThreads := ((numTokens + blockSize - 1) / blockSize) * blockSize
  let pageTable ← Keystone.CLI.array json "page_table"
  let kvCache ← Keystone.CLI.array json "kv_cache"
  -- These limits protect the executable interpreter, not the general theorems.
  if numThreads > 4096 ∨ pageTable.size > 4096 ∨ kvCache.size > 65536 then
    throw "model runner limit exceeded (4096 threads/page-table entries, 65536 KV-cache entries)"
  let cfg : Config := ⟨numTokens, pageSize, numThreads⟩
  let mem : KVMemory := ⟨← pageTable.mapM Json.getNat?, ← kvCache.mapM word⟩
  unless validateLaunch cfg mem do
    throw "invalid gather launch (coverage or physical-page bounds)"
  let schedule ← match Keystone.CLI.optional json "schedule" with
    | none => pure (roundRobin cfg)
    | some value => do
      let items ← value.getArr?
      if items.size > 32768 then throw "schedule exceeds model runner limit (32768 steps)"
      pure (← items.toList.mapM Json.getNat?)
  let common := [("num_threads", toJson numThreads), ("steps", toJson schedule.length),
    ("expected_output", toJson ((expectedOutput cfg mem).map UInt32.toNat))]
  match run cfg mem schedule initialState with
  | .error fault => return Json.mkObj (common ++ [
      ("status", toJson "fault"), ("fault", faultJson fault)])
  | .ok (s, accesses) => return Json.mkObj (common ++ [
      ("status", toJson (if completed cfg s then "completed" else "incomplete")),
      ("output", toJson ((outputEntries cfg s).map (Option.map UInt32.toNat))),
      ("accesses", toJson (accesses.map accessJson))])

end GPUCommand

def main : IO UInt32 := Keystone.CLI.serve GPUCommand.handle

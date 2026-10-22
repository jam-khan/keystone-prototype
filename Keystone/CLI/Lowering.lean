import Keystone.Lowering.Gather
import Keystone.Lowering.Compiler
import Keystone.Lowering.Emit
import Keystone.CLI.Json

open Lean Keystone.Lowering
namespace LowerCommand

private def word (json : Json) : Except String UInt64 := do
  let n ← json.getNat?
  if n ≥ UInt64.size then throw "word must fit uint64"
  return UInt64.ofNat n

private def localId (json : Json) : Except String Nat := do
  let n ← json.getNat?
  if n ≥ 128 then throw "runner supports local indices below 128"
  return n

private def single (json : Json) : Except String (String × Json) := do
  match (← json.getObj?).toList with
  | [field] => return field
  | _ => throw "AST node must have exactly one constructor"

private def arguments (json : Json) (count : Nat) : Except String (Array Json) := do
  let values ← json.getArr?
  if values.size ≠ count then throw s!"constructor requires {count} arguments"
  return values

private def expression : Nat → Json → Except String Expr
  | 0, _ => throw "expression exceeds parser depth limit"
  | fuel + 1, json => do
    if let .ok _ := json.getNat? then return .lit (← word json)
    let (tag, value) ← single json
    match tag with
    | "arg" =>
      match ← value.getStr? with
      | "tid" => return .arg .tid
      | "num_tokens" => return .arg .numTokens
      | "page_size" => return .arg .pageSize
      | _ => throw "unknown kernel parameter"
    | "local" => return .local (← localId value)
    | "add" | "mul" | "div" | "mod" =>
      let values ← arguments value 2
      let op := match tag with
        | "add" => Op.add | "mul" => Op.mul | "div" => Op.div | _ => Op.mod
      return .bin op (← expression fuel values[0]!) (← expression fuel values[1]!)
    | _ => throw "unknown expression constructor"

private def command : Nat → Json → Except String Cmd
  | 0, _ => throw "command exceeds parser depth limit"
  | fuel + 1, json => do
    let (tag, value) ← single json
    match tag with
    | "skip" =>
      unless ← value.getBool? do throw "skip must be true"
      return .skip
    | "seq" =>
      let values ← value.getArr?
      if values.size > 128 then throw "sequence exceeds runner limit"
      let commands ← values.toList.mapM (command fuel)
      return commands.foldr Cmd.seq Cmd.skip
    | "set" | "load_page_table" | "load_kv_cache" =>
      let values ← arguments value 2
      let id ← localId values[0]!
      let operand ← expression 64 values[1]!
      return match tag with
        | "set" => .set id operand
        | "load_page_table" => .loadPageTable id operand
        | _ => .loadKVCache id operand
    | "store" =>
      let values ← arguments value 2
      return .store (← expression 64 values[0]!) (← expression 64 values[1]!)
    | "when_lt" =>
      let values ← arguments value 3
      return .whenLt (← expression 64 values[0]!) (← expression 64 values[1]!)
        (← command fuel values[2]!)
    | _ => throw "unknown command constructor"

private def bufferName : Buffer → String
  | .pageTable => "page_table" | .kvCache => "kv_cache" | .output => "output"

private def accessJson (a : Access) : Json := Json.mkObj [
  ("thread", toJson a.thread.toNat), ("buffer", toJson (bufferName a.buffer)),
  ("index", toJson a.index.toNat)]

private def faultJson : Fault → Json
  | .outOfBounds buffer index => Json.mkObj [("kind", toJson "out_of_bounds"),
      ("buffer", toJson (bufferName buffer)), ("index", toJson index.toNat)]
  | .stackUnderflow => Json.mkObj [("kind", toJson "stack_underflow")]
  | .maskUnderflow => Json.mkObj [("kind", toJson "mask_underflow")]

private def resultJson (numTokens : Nat) (result : Result State) : Json :=
  let (state, fields) := match result with
    | .ok state => (state, [("status", toJson "ok")])
    | .error (fault, state) => (state, [("status", toJson "fault"), ("fault", faultJson fault)])
  Json.mkObj (fields ++ [
    ("output", toJson (Array.ofFn fun i : Fin numTokens => (state.output i).toNat)),
    ("accesses", toJson (state.trace.map accessJson))])

/-- Serial thread launches are only the executable test harness. The lowering
theorem itself is per-thread and does not make a scheduling/race-freedom claim. -/
private def launch (execute : Context → State → Result State)
    (ctx : Context) (numThreads : Nat) : Result State :=
  (List.range numThreads).foldlM (fun state tid =>
    execute { ctx with tid := UInt64.ofNat tid } { state with locals := fun _ => 0 }) {}

def handle (json : Json) : Except String Json := do
  Keystone.CLI.object json ["page_size", "num_tokens", "num_threads", "page_table", "kv_cache"]
    ["source"]
  let pageSize ← word (← Keystone.CLI.field json "page_size")
  let numTokens ← Keystone.CLI.nat json "num_tokens"
  let numThreads ← Keystone.CLI.nat json "num_threads"
  let pageTable ← Keystone.CLI.array json "page_table"
  let kvCache ← Keystone.CLI.array json "kv_cache"
  if numTokens > 4096 ∨ numThreads > 4096 ∨ pageTable.size > 4096 ∨ kvCache.size > 65536 then
    throw "lowering runner size limit exceeded"
  let ctx : Context := ⟨0, UInt64.ofNat numTokens, pageSize, ← pageTable.mapM word,
    ← kvCache.mapM (fun value => do
      let n ← value.getNat?
      if n ≥ UInt32.size then throw "KV-cache entry must fit uint32"
      return UInt32.ofNat n)⟩
  let program ← match Keystone.CLI.optional json "source" with
    | none => pure gather
    | some value => command 64 value
  let code := compile program
  if code.length > 4096 then throw "lowered program exceeds instruction limit"
  let isGather := (Keystone.CLI.optional json "source").isNone
  let contract := Keystone.GPU.validateLaunch ⟨numTokens, pageSize.toNat, numThreads⟩
    ⟨ctx.pageTable.map UInt64.toNat, ctx.kvCache⟩
  let sourceResult := resultJson numTokens (launch (source program) ctx numThreads)
  let targetResult := resultJson numTokens (launch (fun ctx state =>
    (target code ctx ⟨state, [], true, []⟩).map Target.state) ctx numThreads)
  return Json.mkObj [("status", toJson "ok"),
    ("program", toJson (if isGather then "gather" else "custom")),
    ("gather_contract", toJson (isGather && contract)),
    ("observable_equivalent", toJson (sourceResult == targetResult)),
    ("source", sourceResult), ("target", targetResult),
    ("instructions", programJson code), ("listing", toJson (emitListing code)),
    ("c_source", toJson (emitC code)), ("cuda_source", toJson (emitCuda code))]

end LowerCommand

def main : IO UInt32 := Keystone.CLI.serve LowerCommand.handle

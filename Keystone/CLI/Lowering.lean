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
      | "lane" => return .arg .lane
      | "tokens" => return .arg .tokens
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
    | "set" | "load_table" | "load_cache" =>
      let values ← arguments value 2
      let id ← localId values[0]!
      let address ← expression 64 values[1]!
      return match tag with
        | "set" => .set id address
        | "load_table" => .loadTable id address
        | _ => .loadCache id address
    | "store" =>
      let values ← arguments value 2
      return .store (← expression 64 values[0]!) (← expression 64 values[1]!)
    | "when_lt" =>
      let values ← arguments value 3
      return .whenLt (← expression 64 values[0]!) (← expression 64 values[1]!)
        (← command fuel values[2]!)
    | _ => throw "unknown command constructor"

private def spaceName : Space → String
  | .table => "table" | .cache => "cache" | .output => "output"

private def accessJson (a : Access) : Json := Json.mkObj [
  ("lane", toJson a.lane.toNat), ("space", toJson (spaceName a.space)),
  ("address", toJson a.address.toNat)]

private def faultJson : Fault → Json
  | .outOfBounds space address => Json.mkObj [("kind", toJson "out_of_bounds"),
      ("space", toJson (spaceName space)), ("address", toJson address.toNat)]
  | .stackUnderflow => Json.mkObj [("kind", toJson "stack_underflow")]
  | .maskUnderflow => Json.mkObj [("kind", toJson "mask_underflow")]

private def resultJson (n : Nat) (result : Result State) : Json :=
  let (state, fields) := match result with
    | .ok state => (state, [("status", toJson "ok")])
    | .error (fault, state) => (state, [("status", toJson "fault"), ("fault", faultJson fault)])
  Json.mkObj (fields ++ [("output", toJson (Array.ofFn fun i : Fin n => (state.output i).toNat)),
    ("accesses", toJson (state.trace.map accessJson))])

/-- Serial lane launches are only the executable test harness. The lowering
theorem itself is per-lane and does not make a scheduling/race-freedom claim. -/
private def launch (execute : Context → State → Result State)
    (ctx : Context) (lanes : Nat) : Result State :=
  (List.range lanes).foldlM (fun state lane =>
    execute { ctx with lane := UInt64.ofNat lane } { state with locals := fun _ => 0 }) {}

def handle (json : Json) : Except String Json := do
  Keystone.CLI.object json ["page_size", "tokens", "lanes", "table", "cache"] ["source"]
  let pageSize ← word (← Keystone.CLI.field json "page_size")
  let tokens ← Keystone.CLI.nat json "tokens"
  let lanes ← Keystone.CLI.nat json "lanes"
  let table ← Keystone.CLI.array json "table"
  let cache ← Keystone.CLI.array json "cache"
  if tokens > 4096 ∨ lanes > 4096 ∨ table.size > 4096 ∨ cache.size > 65536 then
    throw "lowering runner size limit exceeded"
  let ctx : Context := ⟨0, UInt64.ofNat tokens, pageSize, ← table.mapM word,
    ← cache.mapM (fun value => do
      let n ← value.getNat?
      if n ≥ UInt32.size then throw "cache payload must fit uint32"
      return UInt32.ofNat n)⟩
  let program ← match Keystone.CLI.optional json "source" with
    | none => pure gather
    | some value => command 64 value
  let code := compile program
  if code.length > 4096 then throw "lowered program exceeds instruction limit"
  let isGather := (Keystone.CLI.optional json "source").isNone
  let contract := Keystone.GPU.validateInput ⟨tokens, pageSize.toNat, lanes⟩
    ⟨ctx.table.map UInt64.toNat, ctx.cache⟩
  let sourceResult := resultJson tokens (launch (source program) ctx lanes)
  let targetResult := resultJson tokens (launch (fun ctx state =>
    (target code ctx ⟨state, [], true, []⟩).map Target.state) ctx lanes)
  return Json.mkObj [("status", toJson "ok"),
    ("program", toJson (if isGather then "gather" else "custom")),
    ("gather_contract", toJson (isGather && contract)),
    ("observable_equivalent", toJson (sourceResult == targetResult)),
    ("source", sourceResult), ("target", targetResult),
    ("instructions", programJson code), ("listing", toJson (emitListing code)),
    ("c_source", toJson (emitC code)), ("cuda_source", toJson (emitCuda code))]

end LowerCommand

def main : IO UInt32 := Keystone.CLI.serve LowerCommand.handle

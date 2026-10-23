import Keystone.GPU.KVGather -- Source runs used to generate expected results.
import Keystone.Compile.Emit -- emitC generates the C source.
import Lean.Data.Json -- JSON encoding for the --oracle output.

open Keystone GPU Lean

private def num (n : Nat) : Json := toJson n
private def nums (ns : List Nat) : Json := toJson ns
private def object (fields : List (String × Json)) : Json := Json.mkObj fields

private def stage : Instr → Nat
  | .guard => 0 | .page => 1 | .table => 2 | .kvIndex => 3
  | .load => 4 | .store => 5 | .done => 6

private def accessJson (a : Access) : Json :=
  nums [a.thread, (match a.buffer with | .pageTable => 0 | .kvCache => 1 | .output => 2), a.index]

private def threadJson (t : Thread) : Json :=
  nums [stage t.instr, t.round, t.logicalPage, t.physicalPage, t.kvIndex, t.entry.toNat]

private def fixture (name : String) (cfg : Config) (mem : KVMemory)
    (schedule : List Nat) : Json :=
  let result := match GPU.run cfg mem schedule initialState with
    | .error (.invalidThread tid) => object [("status", num 1), ("thread", num tid)]
    | .error (.outOfBounds access) => object [("status", num 2), ("access", accessJson access)]
    | .ok (s, accesses) => object [
        ("status", num 0),
        ("threads", .arr ((List.range cfg.numThreads).map (threadJson ∘ s.threads)).toArray),
        ("output", .arr ((outputEntries cfg s).map fun x => match x with
          | none => .null | some value => num value.toNat)),
        ("trace", .arr (accesses.map accessJson).toArray)]
  object [("name", toJson name),
    ("config", nums [cfg.numTokens, cfg.pageSize, cfg.numThreads]),
    ("pageTable", toJson mem.pageTable), ("kvCache", toJson (mem.kvCache.map UInt32.toNat)),
    ("schedule", nums schedule), ("expected", result)]

/-- Small differential oracle from the original GPU model, including partial runs and faults. -/
private def oracle : Json := Id.run do
  let cfg : Config := ⟨8, 2, 5⟩
  let mem : KVMemory := ⟨#[2, 0, 3, 1], #[10, 11, 20, 21, 30, 31, 40, 41]⟩
  let padded : Config := ⟨5, 2, 8⟩
  return .arr #[
    fixture "grid-stride" cfg mem (roundRobin cfg),
    fixture "reverse" cfg mem (roundRobin cfg).reverse,
    fixture "padding" padded mem (roundRobin padded),
    fixture "starvation" cfg mem (List.replicate 13 0),
    fixture "partial" cfg mem ((roundRobin cfg).take 23),
    fixture "invalid-thread" cfg mem [5],
    fixture "page-bounds" cfg { mem with pageTable := #[] } [0, 0, 0],
    fixture "cache-bounds" padded { mem with pageTable := #[2, 0, 7] } (roundRobin padded),
    fixture "zero-page-size" ⟨1, 0, 1⟩ mem (List.replicate 7 0),
    fixture "empty" ⟨0, 2, 3⟩ mem [0, 1, 2]]

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  match args with
  | [] => stdout.putStr Compile.emitC; return 0
  | ["--oracle"] => stdout.putStrLn oracle.compress; return 0
  | _ => (← IO.getStderr).putStrLn "usage: emit_c [--oracle]"; return 1

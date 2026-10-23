import Keystone.GPU.KVGather -- Source stages, kernel state, and launch configuration.
import Keystone.Compile.Target -- Target instructions and their interpreter.

namespace Keystone.Compile

/-- Lower `tid + round * numThreads` into two register operations. -/
def computeToken : List Instruction :=
  [.binary .mul .temp (.register .round) .numThreads,
   .binary .add .temp .threadId (.register .temp)]

/-- Instruction selection for the stages of the already-proved GPU kernel. -/
def compile : GPU.Instr → List Instruction
  | .guard => computeToken ++
      [.branchLt (.register .temp) .numTokens .page .done]
  | .page => computeToken ++
      [.binary .div .logicalPage (.register .temp) .pageSize, .jump .table]
  | .table =>
      [.readPageTable .physicalPage (.register .logicalPage), .jump .kvIndex]
  | .kvIndex => computeToken ++
      [.binary .mod .temp (.register .temp) .pageSize,
       .binary .mul .kvIndex (.register .physicalPage) .pageSize,
       .binary .add .kvIndex (.register .kvIndex) (.register .temp), .jump .load]
  | .load => [.readKVCache (.register .kvIndex), .jump .store]
  | .store => computeToken ++
      [.storeOutput (.register .temp),
       .binary .add .round (.register .round) (.constant 1), .jump .guard]
  | .done => []

/-- One scheduled turn executes the block for the thread's current GPU stage. -/
def step (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat) (s : GPU.KernelState) :
    Except GPU.Fault (GPU.KernelState × List GPU.Access) := do
  if tid ≥ cfg.numThreads then throw (.invalidThread tid)
  let (frame, accesses) ← executeBlock cfg mem tid (compile (s.threads tid).instr) ⟨s, 0⟩
  return (frame.kernel, accesses)

/-- Same schedules, state, memory, events, and faults as `GPU.run`. -/
def run (cfg : GPU.Config) (mem : GPU.KVMemory) :
    List Nat → GPU.KernelState → Except GPU.Fault (GPU.KernelState × List GPU.Access)
  | [], s => .ok (s, [])
  | tid :: schedule, s => do
    let (next, accesses) ← step cfg mem tid s
    let (last, more) ← run cfg mem schedule next
    return (last, accesses ++ more)

end Keystone.Compile

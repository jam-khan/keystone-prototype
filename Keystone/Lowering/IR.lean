import Keystone.GPU.KVGather

namespace Keystone.Lowering

/-- Existing thread registers, plus one temporary used inside a compiled block. -/
inductive Register where
  | round | logicalPage | physicalPage | kvIndex | temp
  deriving Repr, DecidableEq

inductive Operand where
  | constant (value : Nat)
  | threadId | numTokens | pageSize | numThreads
  | register (reg : Register)
  deriving Repr, DecidableEq

inductive Arithmetic where
  | add | mul | div | mod
  deriving Repr, DecidableEq

/-- Target operations. `GPU.Instr` names the destination blocks. -/
inductive Instruction where
  | binary (op : Arithmetic) (dest : Register) (lhs rhs : Operand)
  | readPageTable (dest : Register) (index : Operand)
  | readKVCache (index : Operand)
  | storeOutput (index : Operand)
  | jump (next : GPU.Instr)
  | branchLt (lhs rhs : Operand) (yes no : GPU.Instr)
  deriving Repr, DecidableEq

/-- The actual GPU state, with temporary storage for the current block. -/
structure Frame where
  kernel : GPU.KernelState
  temp : Nat := 0

def readRegister (frame : Frame) (tid : Nat) : Register → Nat
  | .round => (frame.kernel.threads tid).round
  | .logicalPage => (frame.kernel.threads tid).logicalPage
  | .physicalPage => (frame.kernel.threads tid).physicalPage
  | .kvIndex => (frame.kernel.threads tid).kvIndex
  | .temp => frame.temp

def writeRegister (frame : Frame) (tid : Nat) (reg : Register) (value : Nat) : Frame :=
  let thread := frame.kernel.threads tid
  match reg with
  | .round => { frame with kernel := GPU.withThread frame.kernel tid { thread with round := value } }
  | .logicalPage => { frame with kernel := GPU.withThread frame.kernel tid { thread with logicalPage := value } }
  | .physicalPage => { frame with kernel := GPU.withThread frame.kernel tid { thread with physicalPage := value } }
  | .kvIndex => { frame with kernel := GPU.withThread frame.kernel tid { thread with kvIndex := value } }
  | .temp => { frame with temp := value }

def operandValue (cfg : GPU.Config) (tid : Nat) (frame : Frame) : Operand → Nat
  | .constant value => value
  | .threadId => tid
  | .numTokens => cfg.numTokens
  | .pageSize => cfg.pageSize
  | .numThreads => cfg.numThreads
  | .register reg => readRegister frame tid reg

def arithmeticValue : Arithmetic → Nat → Nat → Nat
  | .add, a, b => a + b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b

def jump (frame : Frame) (tid : Nat) (next : GPU.Instr) : Frame :=
  let thread := { frame.kernel.threads tid with instr := next }
  { frame with kernel := GPU.withThread frame.kernel tid thread }

/-- Execute a target operation independently of `GPU.step`. -/
def executeInstruction (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat)
    (op : Instruction) (frame : Frame) : Except GPU.Fault (Frame × Option GPU.Access) := do
  let value := operandValue cfg tid frame
  match op with
  | .binary op dest lhs rhs =>
    return (writeRegister frame tid dest (arithmeticValue op (value lhs) (value rhs)), none)
  | .readPageTable dest index =>
    let index := value index
    let access : GPU.Access := ⟨tid, .pageTable, index⟩
    if index ≥ mem.pageTable.size then throw (.outOfBounds access)
    return (writeRegister frame tid dest mem.pageTable[index]!, some access)
  | .readKVCache index =>
    let index := value index
    let access : GPU.Access := ⟨tid, .kvCache, index⟩
    if index ≥ mem.kvCache.size then throw (.outOfBounds access)
    let kernel := GPU.withThread frame.kernel tid
      { frame.kernel.threads tid with entry := mem.kvCache[index]! }
    return ({ frame with kernel }, some access)
  | .storeOutput index =>
    let index := value index
    let access : GPU.Access := ⟨tid, .output, index⟩
    if index ≥ cfg.numTokens then throw (.outOfBounds access)
    let kernel := GPU.withOutput frame.kernel index (frame.kernel.threads tid).entry
    return ({ frame with kernel }, some access)
  | .jump next => return (jump frame tid next, none)
  | .branchLt lhs rhs yes no =>
    return (jump frame tid (if value lhs < value rhs then yes else no), none)

/-- A block finishes before the scheduler selects another thread. -/
def executeBlock (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat) :
    List Instruction → Frame → Except GPU.Fault (Frame × List GPU.Access)
  | [], frame => .ok (frame, [])
  | op :: rest, frame => do
    let (next, access) ← executeInstruction cfg mem tid op frame
    let (last, accesses) ← executeBlock cfg mem tid rest next
    return (last, access.toList ++ accesses)

end Keystone.Lowering

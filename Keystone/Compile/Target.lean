import Keystone.GPU.KVGather

namespace Keystone.Compile

/--
  Names of mutable variables: GPU thread fields plus scratch `temp`.
  Example: `.binary .div .logicalPage (.register .temp) .pageSize`:
  - `.logicalPage` names the variable to write.
  - `.register .temp` uses `Operand.register` (defined below) to read `temp`.
  The assignment is `logicalPage := temp / pageSize`.

  So, it reads `temp` from `register` and then, divides it by `pageSize`
  and assigns it to `logicalPage`.

  Below `Register` essentially keeps track of `mutable variables`
-/
inductive Register where
  | round
  | logicalPage
  | physicalPage
  | kvIndex
  | temp
  deriving Repr, DecidableEq

/--
  `Operand` describes where an instruction gets an input value:
    a constant, thread ID, launch config, or register.

  Example:
    `.binary .add .temp .threadId (.register .round)`
    means `temp := threadId + round`.
-/
inductive Operand where
  | constant (value : Nat)
  | threadId
  | numTokens
  | pageSize
  | numThreads
  | register (reg : Register)
  deriving Repr, DecidableEq

inductive Arithmetic where
  | add | mul | div | mod
  deriving Repr, DecidableEq

/--
  Each `Instruction` is single action in the compiled program.

  `binary` - calculate and assign
  Example:
    `.binary .add .round (.register round) (.constant 1)`
    means `round := round + 1`

  `readPageTable` - look up a physical page
  Example:
    `.readPageTable .physicalPage (.register .logicalPage)`
    means `physicalPage := pageTable[logicalPage]`

  `readKVCache` - read the actual cached data
  Example:
    `.readKVCache (.register .kvIndex)`
    means `thread.entry := kvCache[kvIndex]`

  `storeOutput` - write that data to the output
  Example:
    `.storeOutput (.register .temp)`
    means `output[temp] := thread.entry`

  `jump` - choose the next kernel stage
  Example:
    `.jump .table`
    means `thread.instr := GPU.Instr.table`

  `branchLt` - choose between two stages based on if value is less than numTokens
  Example:
    `.branchLt (.register .temp) .numTokens .page .done`
    means
      if temp < numTokens:
        next stage := page
      else:
        next stage := done
-/
inductive Instruction where
  | binary        (op : Arithmetic) (dest : Register) (lhs rhs : Operand)
  | readPageTable (dest : Register) (index : Operand)
  | readKVCache   (index : Operand)
  | storeOutput   (index : Operand)
  | jump          (next : GPU.Instr)
  | branchLt      (lhs rhs : Operand) (yes no : GPU.Instr)
  deriving Repr, DecidableEq

structure Frame where
  kernel : GPU.KernelState -- existing threads and output
  temp   : Nat := 0        -- extra scratch variable for this block

/-
  Register is stored in a kernel state,
  and accessed via threadId.

  Each Register maps to a field in the Thread structure,
  so basically each thread has properties.

  take frame, extract kernel state, extract threads,
  and then, access the exact thread state by indexing
  via `tid/threadId`.
-/
def readRegister (frame : Frame) (threadid : Nat) : Register → Nat
  | .round          => (frame.kernel.threads threadid).round
  | .logicalPage    => (frame.kernel.threads threadid).logicalPage
  | .physicalPage   => (frame.kernel.threads threadid).physicalPage
  | .kvIndex        => (frame.kernel.threads threadid).kvIndex
  | .temp           => frame.temp

/-
  Write register essentially means take an existing
  frame, thread id, register and value, then,
  return a new frame with updated value for a particular thread.
-/
def writeRegister (frame : Frame) (tid : Nat) (reg : Register) (value : Nat) : Frame :=
  let thread := frame.kernel.threads tid
  match reg with
  -- update value of round for particular thread, rest are similar
  | .round          =>
      { frame with kernel := GPU.withThread frame.kernel tid { thread with round := value } }
  | .logicalPage    =>
      { frame with kernel := GPU.withThread frame.kernel tid { thread with logicalPage := value } }
  | .physicalPage   =>
      { frame with kernel := GPU.withThread frame.kernel tid { thread with physicalPage := value } }
  | .kvIndex        =>
      { frame with kernel := GPU.withThread frame.kernel tid { thread with kvIndex := value } }
  | .temp           =>
      { frame with temp := value }

/-
  Essentially execute the operand part and give concrete value
-/
def operandValue (cfg : GPU.Config) (tid : Nat) (frame : Frame) : Operand → Nat
  | .constant value => value
  | .threadId       => tid
  | .numTokens      => cfg.numTokens
  | .pageSize       => cfg.pageSize
  | .numThreads     => cfg.numThreads
  | .register reg   => readRegister frame tid reg

def arithmeticValue : Arithmetic → Nat → Nat → Nat
  | .add, a, b => a + b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b

def jump (frame : Frame) (tid : Nat) (next : GPU.Instr) : Frame :=
  let thread := { frame.kernel.threads tid with instr := next }
  { frame with kernel := GPU.withThread frame.kernel tid thread }

/--
  Execute one IR instruction independently of `GPU.step`.

  Success: return the updated frame and an optional memory-access record.
    `some access` records a page-table read, cache read, or output write.
    `none` means only registers or the next stage changed.
  Failure: return a fault if a memory index is out of bounds.
-/
def executeInstruction (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat)
    (op : Instruction) (frame : Frame) : Except GPU.Fault (Frame × Option GPU.Access) := do
  -- Resolve an operand, e.g. `value (.register .round)` reads this thread's round.
  let value := operandValue cfg tid frame
  match op with

  | .binary arithmetic dest lhs rhs =>
    -- Read both operands, calculate the result, then assign it to `dest`.
    let result := arithmeticValue arithmetic (value lhs) (value rhs)
    let nextFrame := writeRegister frame tid dest result
    return (nextFrame, none)

  | .readPageTable dest index =>
    -- dest := pageTable[index]
    let index := value index
    -- The record identifies the thread, buffer, and index being accessed.
    let access : GPU.Access := ⟨tid, .pageTable, index⟩
    if index ≥ mem.pageTable.size then
      throw (.outOfBounds access)

    let physicalPage := mem.pageTable[index]!
    let nextFrame := writeRegister frame tid dest physicalPage
    return (nextFrame, some access)

  | .readKVCache index =>
    -- thread.entry := kvCache[index]
    let index := value index
    let access : GPU.Access := ⟨tid, .kvCache, index⟩
    if index ≥ mem.kvCache.size then
      throw (.outOfBounds access)

    let thread := { frame.kernel.threads tid with entry := mem.kvCache[index]! }
    let kernel := GPU.withThread frame.kernel tid thread
    return ({ frame with kernel }, some access)

  | .storeOutput index =>
    -- output[index] := thread.entry
    let index := value index
    let access : GPU.Access := ⟨tid, .output, index⟩
    if index ≥ cfg.numTokens then
      throw (.outOfBounds access)

    let entry := (frame.kernel.threads tid).entry
    let kernel := GPU.withOutput frame.kernel index entry
    return ({ frame with kernel }, some access)

  | .jump next =>
    -- Set thread.instr := next; that stage is not executed here.
    return (jump frame tid next, none)

  | .branchLt lhs rhs yes no =>
    -- If lhs < rhs, select the `yes` stage; otherwise select `no`.
    let next := if value lhs < value rhs then yes else no
    return (jump frame tid next, none)

/-- A block finishes before the scheduler selects another thread. -/
def executeBlock (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat) :
    List Instruction → Frame → Except GPU.Fault (Frame × List GPU.Access)
  | [], frame => .ok (frame, [])
  | op :: rest, frame => do
    let (next, access)    ← executeInstruction cfg mem tid op frame
    let (last, accesses)  ← executeBlock cfg mem tid rest next
    return (last, access.toList ++ accesses)

end Keystone.Compile

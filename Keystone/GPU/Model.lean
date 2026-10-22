import Std

/-!
# Paged gather: the basics

**What the kernel computes** (page size `B`):
`output[tid] = cache[pageTable[tid / B] * B + tid % B]`

**Sizes**
- `numElements` = total elements to gather (e.g. 5)
- `pageSize`    = elements per page (e.g. 2), so 5 elements fill 3 pages: 2 + 2 + 1
- `numThreads`  = threads launched (e.g. 8)
- padded threads = `numThreads - numElements` (e.g. 8 - 5 = 3)

**Threads**
- `tid` = a thread's global ID (CUDA: `blockIdx.x * blockDim.x + threadIdx.x`).
- One thread handles exactly one element, ever: thread `tid` gathers element `tid`.
- Padded thread = thread with `tid ≥ numElements`. It has no element and touches no memory.
- Padding compares threads to *elements* (`numElements`), not to pages.
- Several threads share a page: thread `tid` is in logical page `tid / B`, offset `tid % B`.

**Pages**
- Logical page = where an element sits in the gathered order.
- Physical page = where it actually sits in `cache`.
- `pageTable[logical] = physical`.

**Instructions (`pc` = the instruction a thread runs NEXT)**
`.guard → .index → .table → .address → .load → .store → .done`
- `.guard`   : `tid < numElements`? go to `.index`; else go straight to `.done`. No memory read.
- `.index`   : `page := tid / B`. No memory read.
- `.table`   : `physical := pageTable[page]`. Reads page table.
- `.address` : `address := physical * B + tid % B`. No memory read.
- `.load`    : `value := cache[address]`. Reads cache.
- `.store`   : `output[tid] := value`. Writes output.
- Each scheduled turn moves a thread ONE arrow, so 6 turns reach `.done`.

**Machine and scheduling**
- `Thread` = one thread's state: its `pc` plus the values it has computed so far.
- `init` already gives every thread ID a fresh state (`pc = .guard`, rest 0).
- `withThread` replaces one thread's state; it never adds one.
- `Access` = one memory read/write: which thread, which `Buffer`, which index.
- `run` takes a schedule list like `[0, 1, 2, …]`; each entry lets that thread take one step.

**Running example** (`numElements = 5`, `pageSize = 2`, `numThreads = 8`)
```
pageTable = #[2, 0, 1]
cache     = #[10, 11, 20, 21, 30, 31]   -- physical pages: 0 = [10,11], 1 = [20,21], 2 = [30,31]
output    = #[30, 31, 10, 11, 20]
```

| threads | logical page | physical page | role   |
|---------|--------------|---------------|--------|
| 0, 1    | 0            | 2             | real   |
| 2, 3    | 1            | 0             | real   |
| 4       | 2            | 1             | real   |
| 5, 6, 7 | —            | —             | padded |

Thread 3, one row per turn:

| `pc` before | does                     | thread state after             |
|-------------|--------------------------|--------------------------------|
| `.guard`    | 3 < 5, has work          | `pc = .index`                  |
| `.index`    | page = 3 / 2 = 1         | `page = 1`, `pc = .table`      |
| `.table`    | `pageTable[1]` = 0       | `physical = 0`, `pc = .address`|
| `.address`  | 0 * 2 + 3 % 2 = 1        | `address = 1`, `pc = .load`    |
| `.load`     | `cache[1]` = 11          | `value = 11`, `pc = .store`    |
| `.store`    | `output[3] := 11`        | `pc = .done`                   |
-/

namespace Keystone.GPU

/--
  `Config` is shape of a gather launch.

  What does Gather mean in this context?
  `read values from selected location and collect in order`

  Example `{ numElements := 5, pageSize := 2, numThreads := 8 }`:
  - Threads 0–4 gather elements; padded threads 5–7 skip memory accesses.
  - Element 3 is in logical page `3 / 2 = 1`, at offset `3 % 2 = 1`.
    The page table maps logical pages to physical cache pages.
-/
structure Config where
  numElements : Nat -- number of logical elements to gather
  pageSize    : Nat -- number of elements in each cache page
  numThreads  : Nat -- number of launched GPU threads, including padding
  deriving Repr, DecidableEq

/--
  `Input` contains data for gather to read

  Let's say we have pageSize = 2,
  so  pageTable = #[2, 0, 1]
      cache     = #[10, 11, 20, 21, 30, 31]

      page 0 will consist of 10, 11
      page 1 will consist of 20, 21 and so on
-/
structure Input where
  pageTable   : Array Nat    -- map of each logical page number to a physical page number
  cache       : Array UInt32 -- store of unsigned 32-bit values
  deriving Repr, DecidableEq

-- Maps from logical page to physical page
def physicalPage (input : Input) (logicalPage : Nat) : Nat :=
  input.pageTable[logicalPage]!

/--
  Program counter to keep track of which
  instruction to execute for a thread
-/
inductive PC where
  | guard -- check whether this thread has an element to gather
  | index -- compute element's logical page number
  | table -- read the page table to find the physical page from logical one
  | address -- compute the element's position in the cache
  | load    -- read the value from cache
  | store   -- write the value to the output
  | done    -- no work remains
  deriving Repr, DecidableEq

/--
  `Thread` stores one GPU thread's current state: its next instruction
  and the intermediate values it has computed.
-/
structure Thread where
  pc       : PC   := .guard -- next instruction
  page     : Nat  := 0      -- logical page number
  physical : Nat  := 0      -- physical page number in page table
  address  : Nat  := 0      -- element index in cache
  value    : UInt32 := 0    -- value read from cache
  deriving Repr, DecidableEq

structure Machine where
  threads : Nat → Thread        -- mapping from thread ID to its state
  -- tries to find output at that position
  -- initially, output 0 = none and then thread 0 stores, so output 0 = some 30
  output  : Nat → Option UInt32

/-- default/initial state of a machine
  `threads` all are just empty `Thread`, so fresh state of each thread essentially
  `output` is none because no thread has stored anything yet
--/
def init : Machine := ⟨fun _ => {}, fun _ => none⟩

-- Set thread `tid`'s state in machine `m`, replacing its old state
def withThread (m : Machine) (tid : Nat) (thread : Thread) : Machine :=
  { m with threads := fun j => if j = tid then thread else m.threads j }

-- Add (thread, output) info to a machine `m`
def withOutput (m : Machine) (tid : Nat) (value : UInt32) : Machine :=
  { m with output := fun j => if j = tid then some value else m.output j }

-- Specifies which buffer is accessed
inductive Buffer where
  | pageTable -- logical to physical page mapping
  | cache     -- stored values
  | output    -- gathered results
  deriving Repr, DecidableEq

/--
  Records which thread accessed which buffer element, where address is
  the element index.
  For example, { thread := 3, buffer := .cache, address := 1 }
  this means thread 3 accessed cache at the element index 1
-/
structure Access where
  thread    : Nat
  buffer    : Buffer
  address   : Nat
  deriving Repr, DecidableEq

/--
  Fault is an invalid operation during kernel execution
-/
inductive Fault where
  | invalidThread (tid : Nat)     -- execution on a wrong thread for example, or some thread not launched
  | outOfBounds (access : Access) -- accessing an element on an index which is out of bounds
  deriving Repr, DecidableEq


/-- Cache index = physical page × page size + offset within the page.
For page size `B`: `pageTable[tid / B] * B + tid % B`. -/
def cacheIndex (cfg : Config) (input : Input) (tid : Nat) : Nat :=
  physicalPage input (tid / cfg.pageSize) * cfg.pageSize + tid % cfg.pageSize

/--
  Takes threadid, input and config, and
  returns the value stored in cache
-/
def expectedValue (cfg : Config) (input : Input) (tid : Nat) : UInt32 :=
  input.cache[cacheIndex cfg input tid]!

/--
  output kernel should produce, basically an array of values
-/
def expectedOutput (cfg : Config) (input : Input) : Array UInt32 :=
  Array.ofFn (fun t : Fin cfg.numElements => expectedValue cfg input t)

/--
  Run thread `tid`'s next instruction.
  Returns the new machine and the memory access made, if any;
  throws a `Fault` for an unlaunched thread or an out-of-bounds access.
-/
def step (cfg : Config) (input : Input) (tid : Nat) (m : Machine)
    : Except Fault (Machine × Option Access) := do
  if tid ≥ cfg.numThreads then throw (.invalidThread tid)
  let thread := m.threads tid
  match thread.pc with
  | .guard =>
    -- if tid < numElements then next instruction is .index
    -- padded threads (tid ≥ numElements) have no element, so they finish immediately
    let nextThread  := { thread with pc := if tid < cfg.numElements then .index else .done }
    let newMachine  := withThread m tid nextThread
    return (newMachine, none)
  | .index =>
    -- this part works out which logical page has the thread's element
    let nextThread  := { thread with pc := .table, page := tid / cfg.pageSize }
    let newMachine  := withThread m tid nextThread
    return (newMachine, none)
  | .table =>
    -- read the page table: logical page → physical page
    let access : Access := ⟨tid, .pageTable, thread.page⟩
    if thread.page ≥ input.pageTable.size then throw (.outOfBounds access)
    let nextThread  := { thread with pc := .address, physical := physicalPage input thread.page }
    let newMachine  := withThread m tid nextThread
    return (newMachine, some access)
  | .address =>
    -- cache index = physical page × page size + offset within the page
    let offset      := tid % cfg.pageSize
    let nextThread  := { thread with pc := .load, address := thread.physical * cfg.pageSize + offset }
    let newMachine  := withThread m tid nextThread
    return (newMachine, none)
  | .load =>
    -- read the element from the cache
    let access : Access := ⟨tid, .cache, thread.address⟩
    if thread.address ≥ input.cache.size then throw (.outOfBounds access)
    let nextThread  := { thread with pc := .store, value := input.cache[thread.address]! }
    let newMachine  := withThread m tid nextThread
    return (newMachine, some access)
  | .store =>
    -- write the element to output slot `tid`
    let access : Access := ⟨tid, .output, tid⟩
    if tid ≥ cfg.numElements then throw (.outOfBounds access)
    let nextThread  := { thread with pc := .done }
    let newMachine  := withOutput (withThread m tid nextThread) tid thread.value
    return (newMachine, some access)
  | .done => return (m, none)

/-- Replay a supplied interleaving; the schedule need not be fair or complete. -/
def run (cfg : Config) (input : Input) :
    List Nat → Machine → Except Fault (Machine × List Access)
  | [], m => .ok (m, [])
  | tid :: schedule, m => do
    let (next, access) ← step cfg input tid m
    let (last, accesses) ← run cfg input schedule next
    return (last, access.toList ++ accesses)

/-- Give each thread six turns, enough to reach `done` from `guard`. -/
def roundRobin (cfg : Config) : List Nat :=
  (List.replicate 6 (List.range cfg.numThreads)).flatten

def completed (cfg : Config) (m : Machine) : Bool :=
  (List.range cfg.numThreads).all (fun t => (m.threads t).pc == .done)

def outputValues (cfg : Config) (m : Machine) : Array (Option UInt32) :=
  Array.ofFn (fun t : Fin cfg.numElements => m.output t)

/-- Every listed physical page must be fully allocated, including unused entries. -/
def ValidInput (cfg : Config) (input : Input) : Prop :=
  0 < cfg.pageSize ∧ cfg.numElements ≤ cfg.numThreads ∧
  cfg.numElements ≤ input.pageTable.size * cfg.pageSize ∧
  ∀ p : Fin input.pageTable.size,
    physicalPage input p * cfg.pageSize + cfg.pageSize ≤ input.cache.size

instance (cfg : Config) (input : Input) : Decidable (ValidInput cfg input) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∀ _p : Fin input.pageTable.size, _))

def validateInput (cfg : Config) (input : Input) : Bool := decide (ValidInput cfg input)

@[simp] theorem validateInput_eq_true : validateInput cfg input = true ↔ ValidInput cfg input := by
  simp [validateInput]

end Keystone.GPU

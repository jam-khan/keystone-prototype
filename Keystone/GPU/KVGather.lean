import Std

/-!
# KV gather: one GPU kernel from LLM inference

**What this file is:** a model of one GPU kernel, the *paged KV gather*.
During LLM inference, each request's KV-cache entries (one per token) are
scattered across pages of the shared KV cache. This kernel copies one
request's entries back into a contiguous `output`, in token order.
Simplification: one token's entry is a single `UInt32` here; in vLLM it is
that token's key and value vectors.

**What the kernel computes** (page size `B`):
`output[tid] = kvCache[pageTable[tid / B] * B + tid % B]`


**Sizes**
- `numTokens`  = tokens in this request = entries to gather (e.g. 5)
- `pageSize`   = tokens per page (e.g. 2), so 5 tokens fill 3 pages: 2 + 2 + 1
- `numThreads` = threads launched (e.g. 8)
- padded threads = `numThreads - numTokens` (e.g. 8 - 5 = 3)

5 6 7 8 10
0  1  2  3  4

**Threads**
- `tid` = a thread's global ID (CUDA: `blockIdx.x * blockDim.x + threadIdx.x`).
- One thread copies exactly one token's entry, ever: thread `tid` handles token `tid`.
- Padded thread = thread with `tid ≥ numTokens`. It has no token and touches no memory.
- Padding compares threads to *tokens* (`numTokens`), not to pages.
- Several threads share a page: token `tid` is in logical page `tid / B`, offset `tid % B`.

**Memory** (three buffers, all in GPU global memory)
- `kvCache`   = the KV cache: one big pool of pages shared by all requests.
  NOT a hardware cache (L1/L2); the model has none.
- `pageTable` = this request's map from logical page to physical page.
- `output`    = where gathered entries go, in token order.
- `KVMemory`  = the two buffers the kernel reads: `pageTable` and `kvCache`.
- Positions are indices into these arrays (`kvIndex`, `Access.index`), not byte addresses.

**Pages**
- Logical page = which page of *this request* holds the token (tokens 0–1 → page 0, …).
- Physical page = where that page actually sits in `kvCache`.
- `pageTable[logical] = physical`.

**Instructions** (`instr` = the instruction a thread runs NEXT;
GPU papers call this the thread's program counter)
`.guard → .page → .table → .kvIndex → .load → .store → .done`
- `.guard`   : `tid < numTokens`? go to `.page`; else go straight to `.done`. No memory read.
- `.page`    : `logicalPage := tid / B`. No memory read.
- `.table`   : `physicalPage := pageTable[logicalPage]`. Reads page table.
- `.kvIndex` : `kvIndex := physicalPage * B + tid % B`. No memory read.
- `.load`    : `entry := kvCache[kvIndex]`. Reads KV cache.
- `.store`   : `output[tid] := entry`. Writes output.
- Each scheduled turn moves a thread ONE arrow, so 6 turns reach `.done`.

**Kernel state and scheduling**
- `Thread` = one thread's state: its `instr` plus what it has computed so far.
- `KernelState` = every thread's state plus the `output` buffer.
- `initialState` gives every thread ID a fresh state (`instr = .guard`, rest 0).
- `withThread` replaces one thread's state; it never adds one.
- `Access` = one memory read/write: which thread, which `Buffer`, which index.
- `run` takes a schedule list like `[0, 1, 2, …]`; each item lets that thread take one step.

**Running example** (`numTokens = 5`, `pageSize = 2`, `numThreads = 8`)
```
pageTable = #[2, 0, 1]
kvCache   = #[10, 11, 20, 21, 30, 31]   -- physical pages: 0 = [10,11], 1 = [20,21], 2 = [30,31]
output    = #[30, 31, 10, 11, 20]
```

| threads (= tokens) | logical page | physical page | role   |
|--------------------|--------------|---------------|--------|
| 0, 1               | 0            | 2             | real   |
| 2, 3               | 1            | 0             | real   |
| 4                  | 2            | 1             | real   |
| 5, 6, 7            | —            | —             | padded |

Thread 3, one row per turn:

| `instr` before | does                | thread state after                     |
|----------------|---------------------|----------------------------------------|
| `.guard`       | 3 < 5, has a token  | `instr = .page`                        |
| `.page`        | 3 / 2 = 1           | `logicalPage = 1`, `instr = .table`    |
| `.table`       | `pageTable[1]` = 0  | `physicalPage = 0`, `instr = .kvIndex` |
| `.kvIndex`     | 0 * 2 + 3 % 2 = 1   | `kvIndex = 1`, `instr = .load`         |
| `.load`        | `kvCache[1]` = 11   | `entry = 11`, `instr = .store`         |
| `.store`       | `output[3] := 11`   | `instr = .done`                        |
-/

namespace Keystone.GPU

/--
  `Config` is shape of a gather launch.

  What does Gather mean in this context?
  `read entries from selected location and collect in order`

  Example `{ numTokens := 5, pageSize := 2, numThreads := 8 }`:
  - Threads 0–4 each copy one token's entry; padded threads 5–7 skip memory accesses.
  - Token 3 is in logical page `3 / 2 = 1`, at offset `3 % 2 = 1`.
    The page table maps logical pages to physical pages in the KV cache.
-/
structure Config where
  numTokens  : Nat -- tokens in this request; one KV entry per token
  pageSize   : Nat -- tokens per KV-cache page
  numThreads : Nat -- number of launched GPU threads, including padding
  deriving Repr, DecidableEq

/--
  `KVMemory` is the GPU memory the kernel reads:
  this request's page table and the shared KV cache.

  Let's say we have pageSize = 2,
  so  pageTable = #[2, 0, 1]
      kvCache   = #[10, 11, 20, 21, 30, 31]

      page 0 will consist of 10, 11
      page 1 will consist of 20, 21 and so on
-/
structure KVMemory where
  pageTable   : Array Nat    -- map of each logical page number to a physical page number
  kvCache     : Array UInt32 -- KV cache: pool of pages, one UInt32 entry per token slot
  deriving Repr, DecidableEq

-- Maps from logical page to physical page
def physicalPage (mem : KVMemory) (logicalPage : Nat) : Nat :=
  mem.pageTable[logicalPage]!

/--
  Keeps track of which instruction to execute next for a thread
  (GPU papers call this the thread's program counter)
-/
inductive Instr where
  | guard   -- check whether this thread has a token to gather
  | page    -- compute the token's logical page number
  | table   -- read the page table to find the physical page from logical one
  | kvIndex -- compute the token's position in the KV cache
  | load    -- read the token's entry from the KV cache
  | store   -- write the entry to the output
  | done    -- no work remains
  deriving Repr, DecidableEq

/--
  `Thread` stores one GPU thread's current state: its next instruction
  and the intermediate results it has computed.
-/
structure Thread where
  instr        : Instr  := .guard -- next instruction
  logicalPage  : Nat    := 0      -- which page of this request holds my token
  physicalPage : Nat    := 0      -- where that page sits in the KV cache
  kvIndex      : Nat    := 0      -- exact position of my token's entry in the KV cache
  entry        : UInt32 := 0      -- the entry read from the KV cache
  deriving Repr, DecidableEq

/--
  State of the whole running kernel: every thread's state, plus the output buffer.
-/
structure KernelState where
  threads : Nat → Thread        -- mapping from thread ID to its state
  -- tries to find output at that position
  -- initially, output 0 = none and then thread 0 stores, so output 0 = some 30
  output  : Nat → Option UInt32

/-- default/initial state of the kernel
  `threads` all are just empty `Thread`, so fresh state of each thread essentially
  `output` is none because no thread has stored anything yet
--/
def initialState : KernelState := ⟨fun _ => {}, fun _ => none⟩

-- Set thread `tid`'s state in kernel state `s`, replacing its old state
def withThread (s : KernelState) (tid : Nat) (thread : Thread) : KernelState :=
  { s with threads := fun j => if j = tid then thread else s.threads j }

-- Add (thread, output) info to kernel state `s`
def withOutput (s : KernelState) (tid : Nat) (entry : UInt32) : KernelState :=
  { s with output := fun j => if j = tid then some entry else s.output j }

-- Specifies which buffer is accessed
inductive Buffer where
  | pageTable -- logical to physical page mapping
  | kvCache   -- KV-cache entries
  | output    -- gathered entries, in token order
  deriving Repr, DecidableEq

/--
  Records which thread accessed which buffer, and at which index.
  For example, { thread := 3, buffer := .kvCache, index := 1 }
  this means thread 3 accessed the KV cache at index 1
-/
structure Access where
  thread    : Nat
  buffer    : Buffer
  index     : Nat
  deriving Repr, DecidableEq

/--
  Fault is an invalid operation during kernel execution
-/
inductive Fault where
  | invalidThread (tid : Nat)     -- execution on a wrong thread for example, or some thread not launched
  | outOfBounds (access : Access) -- accessing an element on an index which is out of bounds
  deriving Repr, DecidableEq


/-- KV index = physical page × page size + offset within the page.
For page size `B`: `pageTable[tid / B] * B + tid % B`. -/
def kvIndex (cfg : Config) (mem : KVMemory) (tid : Nat) : Nat :=
  physicalPage mem (tid / cfg.pageSize) * cfg.pageSize + tid % cfg.pageSize

/--
  Takes thread id, KV memory and config, and
  returns the entry token `tid` should get from the KV cache
-/
def expectedEntry (cfg : Config) (mem : KVMemory) (tid : Nat) : UInt32 :=
  mem.kvCache[kvIndex cfg mem tid]!

/--
  output kernel should produce, basically an array of entries in token order
-/
def expectedOutput (cfg : Config) (mem : KVMemory) : Array UInt32 :=
  Array.ofFn (fun t : Fin cfg.numTokens => expectedEntry cfg mem t)

/--
  Run thread `tid`'s next instruction.
  Returns the new kernel state and the memory access made, if any;
  throws a `Fault` for an unlaunched thread or an out-of-bounds access.
-/
def step (cfg : Config) (mem : KVMemory) (tid : Nat) (s : KernelState)
    : Except Fault (KernelState × Option Access) := do
  if tid ≥ cfg.numThreads then throw (.invalidThread tid)
  let thread := s.threads tid
  match thread.instr with
  | .guard =>
    -- if tid < numTokens then next instruction is .page
    -- padded threads (tid ≥ numTokens) have no token, so they finish immediately
    let nextThread  := { thread with instr := if tid < cfg.numTokens then .page else .done }
    let newState    := withThread s tid nextThread
    return (newState, none)
  | .page =>
    -- this part works out which logical page has the thread's token
    let nextThread  := { thread with instr := .table, logicalPage := tid / cfg.pageSize }
    let newState    := withThread s tid nextThread
    return (newState, none)
  | .table =>
    -- read the page table: logical page → physical page
    let access : Access := ⟨tid, .pageTable, thread.logicalPage⟩
    if thread.logicalPage ≥ mem.pageTable.size then throw (.outOfBounds access)
    let nextThread  := { thread with
      instr := .kvIndex, physicalPage := physicalPage mem thread.logicalPage }
    let newState    := withThread s tid nextThread
    return (newState, some access)
  | .kvIndex =>
    -- KV index = physical page × page size + offset within the page
    let offset      := tid % cfg.pageSize
    let nextThread  := { thread with
      instr := .load, kvIndex := thread.physicalPage * cfg.pageSize + offset }
    let newState    := withThread s tid nextThread
    return (newState, none)
  | .load =>
    -- read the token's entry from the KV cache
    let access : Access := ⟨tid, .kvCache, thread.kvIndex⟩
    if thread.kvIndex ≥ mem.kvCache.size then throw (.outOfBounds access)
    let nextThread  := { thread with instr := .store, entry := mem.kvCache[thread.kvIndex]! }
    let newState    := withThread s tid nextThread
    return (newState, some access)
  | .store =>
    -- write the entry to output slot `tid`
    let access : Access := ⟨tid, .output, tid⟩
    if tid ≥ cfg.numTokens then throw (.outOfBounds access)
    let nextThread  := { thread with instr := .done }
    let newState    := withOutput (withThread s tid nextThread) tid thread.entry
    return (newState, some access)
  | .done => return (s, none)

/-- Replay a supplied interleaving; the schedule need not be fair or complete. -/
def run (cfg : Config) (mem : KVMemory) :
    List Nat → KernelState → Except Fault (KernelState × List Access)
  | [], s => .ok (s, [])
  | tid :: schedule, s => do
    let (next, access) ← step cfg mem tid s
    let (last, accesses) ← run cfg mem schedule next
    return (last, access.toList ++ accesses)

/-- Give each thread six turns, enough to reach `done` from `guard`. -/
def roundRobin (cfg : Config) : List Nat :=
  (List.replicate 6 (List.range cfg.numThreads)).flatten

def completed (cfg : Config) (s : KernelState) : Bool :=
  (List.range cfg.numThreads).all (fun t => (s.threads t).instr == .done)

def outputEntries (cfg : Config) (s : KernelState) : Array (Option UInt32) :=
  Array.ofFn (fun t : Fin cfg.numTokens => s.output t)

/--
  A launch is valid when pages are non-empty, there is a thread for every token,
  the page table covers every token, and every physical page it lists fits
  inside the KV cache (even pages no token uses).
-/
def ValidLaunch (cfg : Config) (mem : KVMemory) : Prop :=
  0 < cfg.pageSize ∧ cfg.numTokens ≤ cfg.numThreads ∧
  cfg.numTokens ≤ mem.pageTable.size * cfg.pageSize ∧
  ∀ p : Fin mem.pageTable.size,
    physicalPage mem p * cfg.pageSize + cfg.pageSize ≤ mem.kvCache.size

instance (cfg : Config) (mem : KVMemory) : Decidable (ValidLaunch cfg mem) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∀ _p : Fin mem.pageTable.size, _))

def validateLaunch (cfg : Config) (mem : KVMemory) : Bool := decide (ValidLaunch cfg mem)

@[simp] theorem validateLaunch_eq_true :
    validateLaunch cfg mem = true ↔ ValidLaunch cfg mem := by
  simp [validateLaunch]

end Keystone.GPU

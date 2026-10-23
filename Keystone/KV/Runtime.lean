import Keystone.GPU.KVGather -- GPU memory, kernel state, and completion.
import Keystone.Compile.Compiler -- Compile.run executes each job.
import Keystone.KV.Manager -- Leases, tickets, and page-lifetime operations.

/-! Shared cache → ticket page table → Compile.run → GPU completion. -/
namespace Keystone.KV

/-- A ticket supplies the GPU page table; reads use the supplied shared cache. -/
def Ticket.memory (ticket : Ticket) (cache : Array UInt32) : GPU.KVMemory :=
  ⟨(ticket.pages.map Lease.page).toArray, cache⟩

/-- Replace one physical page in the shared pool. The runtime checks its size and lease. -/
def fillPage (cache : Array UInt32) (pageSize page : Nat) (entries : Array UInt32) :
    Array UInt32 :=
  cache.mapIdx fun index old =>
    if index / pageSize = page then entries[index % pageSize]! else old

/-- One submitted gather. `snapshot` states the expected result; execution reads the pool. -/
structure Job where
  ticket : Ticket
  config : GPU.Config
  snapshot : Array UInt32
  kernel : GPU.KernelState := GPU.initialState

def Job.memory (job : Job) : GPU.KVMemory := job.ticket.memory job.snapshot

/-- Shared cache storage and the actual GPU state of each pending operation. -/
structure Runtime where
  manager : State
  pageSize : Nat
  cache : Array UInt32
  jobs : Nat → Option Job

namespace Runtime

def init (capacity pageSize : Nat) : Runtime :=
  ⟨KV.init capacity, pageSize, Array.replicate (capacity * pageSize) 0, fun _ => none⟩

def withJob (r : Runtime) (id : Nat) (job : Option Job) : Runtime :=
  { r with jobs := fun j => if j = id then job else r.jobs j }

/-- Allocate and fill one free page. Its contents stay sealed for this allocation. -/
def allocate (r : Runtime) (owner : Nat) (entries : Array UInt32) : Option (Runtime × Lease) := do
  if entries.size ≠ r.pageSize then none else
  let (manager, lease) ← KV.allocate r.manager owner
  let cache := fillPage r.cache r.pageSize lease.page entries
  pure ({ r with manager, cache }, lease)

/-- Pin the ordered leases and start the existing gather with that exact page table. -/
def launch (r : Runtime) (owner : Nat) (pages : List Lease)
    (numTokens numThreads : Nat) : Option (Runtime × Nat) := do
  if ¬ (0 < r.pageSize ∧ 0 < numThreads ∧ numTokens ≤ pages.length * r.pageSize) then none else
  let (manager, ticket) ← submit r.manager owner pages
  let job : Job := ⟨ticket, ⟨numTokens, r.pageSize, numThreads⟩, r.cache, GPU.initialState⟩
  pure (withJob { r with manager } ticket.id (some job), ticket.id)

/-- Cancellation stops new submissions; pending kernels and their pages remain. -/
def cancel (r : Runtime) (owner : Nat) : Runtime :=
  { r with manager := retire r.manager owner }

inductive Fault where
  | unknownJob (id : Nat)
  | gpu (fault : GPU.Fault)
  deriving Repr, DecidableEq

/-- Execute a chunk of the existing compiled kernel against the current shared pool.
Call again to resume, including after cancellation or another request's allocation. -/
def run (r : Runtime) (id : Nat) (schedule : List Nat) :
    Except Fault (Runtime × List GPU.Access) := do
  let job ← match r.jobs id with
    | some job => pure job
    | none => throw (.unknownJob id)
  let (kernel, accesses) ←
    (Compile.run job.config (job.ticket.memory r.cache) schedule job.kernel).mapError Fault.gpu
  pure (withJob r id (some { job with kernel }), accesses)

/-- Release the ticket only after every modeled GPU thread is done; return its output. -/
def finish (r : Runtime) (id : Nat) : Option (Runtime × Array (Option UInt32)) := do
  let job ← r.jobs id
  if GPU.completed job.config job.kernel then
    pure (withJob { r with manager := complete r.manager id } id none,
      GPU.outputEntries job.config job.kernel)
  else none

end Runtime
end Keystone.KV

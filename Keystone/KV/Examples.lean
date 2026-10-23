import Keystone.GPU.KVGather -- GPU configurations and roundRobin schedules.
import Keystone.KV.Manager -- Lease fields and manager state used by the mutation.
import Keystone.KV.Runtime -- Connected allocation, launch, execution, and completion.

namespace Keystone.KV.Examples

-- The ticket's order and repeated pages become the actual GPU page table.
private def orderedPages : Option (Array (Option UInt32)) := do
  let (r, a) ← (Runtime.init 2 2).allocate 10 #[10, 11]
  let (r, b) ← r.allocate 10 #[20, 21]
  let (r, id) ← r.launch 10 [b, a, b] 5 2
  let (r, _) ← (r.run id (GPU.roundRobin ⟨5, 2, 2⟩)).toOption
  let (_, output) ← r.finish id
  pure output

#guard orderedPages == some #[some 20, some 21, some 10, some 11, some 20]

-- Two readers of A's page; cancel, change an unrelated page, finish in reverse order,
-- then reuse A's page. Every read below goes through the existing Compile.run.
private def cancellation : Option (Array (Option UInt32) × Array (Option UInt32)) := do
  let (r, a) ← (Runtime.init 2 2).allocate 10 #[30, 31]
  let (r, first) ← r.launch 10 [a, a] 4 2
  let (r, second) ← r.launch 10 [a] 2 3
  let (r, _) ← (r.run first [0, 0, 0, 0]).toOption -- thread 0 is about to load
  let r := r.cancel 10
  guard (r.finish first).isNone
  let (r, b) ← r.allocate 20 #[70, 71] -- another page changes the shared cache
  guard (b.page != a.page)
  guard (r.allocate 30 #[90, 91]).isNone
  let (r, _) ← (r.run second (GPU.roundRobin ⟨2, 2, 3⟩).reverse).toOption
  let (r, secondOutput) ← r.finish second
  guard (r.allocate 30 #[90, 91]).isNone -- the first reader still pins A's page
  let (r, _) ← (r.run first (GPU.roundRobin ⟨4, 2, 2⟩)).toOption
  let (r, firstOutput) ← r.finish first
  let (r, c) ← r.allocate 30 #[90, 91]
  guard (c.page == a.page && c.generation != a.generation)
  -- Even with the new owner and page, an old generation cannot name this allocation.
  guard (r.launch 30 [{ c with generation := a.generation }] 2 1).isNone
  guard (r.launch 10 [a] 2 1).isNone -- cancellation also prevents new work for A
  let (r, third) ← r.launch 30 [c] 2 1
  guard (r.finish first).isNone -- an old completion cannot finish the new job
  let (r, _) ← (r.run third (GPU.roundRobin ⟨2, 2, 1⟩)).toOption
  let (_, thirdOutput) ← r.finish third
  guard (thirdOutput == #[some 90, some 91])
  pure (firstOutput, secondOutput)

#guard cancellation == some (#[some 30, some 31, some 30, some 31], #[some 30, some 31])

-- Inject an invalid policy outside the manager: free A while its load is pending.
-- This breaks Runtime.Valid and makes A read B's data from the real shared pool.
private def earlyReuse : Option (Array (Option UInt32)) := do
  let (r, a) ← (Runtime.init 1 2).allocate 10 #[30, 31]
  let (r, id) ← r.launch 10 [a] 2 1
  let (r, _) ← (r.run id [0, 0, 0, 0]).toOption
  let r := { r with manager := { r.manager with allocations := [] } }
  let (r, _) ← r.allocate 20 #[90, 91]
  let (r, _) ← (r.run id (GPU.roundRobin ⟨2, 2, 1⟩)).toOption
  let (_, output) ← r.finish id
  pure output

#guard earlyReuse == some #[some 90, some 91]

-- Reject incomplete page contents and launches whose page table is too short.
#guard ((Runtime.init 1 2).allocate 10 #[1]).isNone
#guard ((Runtime.init 1 2).launch 10 [] 1 1).isNone
#guard ((Runtime.init 1 2).launch 10 [] 0 0).isNone

end Keystone.KV.Examples

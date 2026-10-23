import Keystone.GPU.KVGather -- GPU memory, launch conditions, and source execution.
import Keystone.GPU.Proofs.Kernel -- Invariant, ThreadOK, and step_safe.
import Keystone.Compile.Compiler -- Compiled step/run.
import Keystone.Compile.Properties -- step_eq connects compiled and source execution.
import Keystone.KV.Manager -- Leases, tickets, and ownership invariants.
import Keystone.KV.Runtime -- Ticket.memory and fillPage.

/-! Supporting proofs: retained pages make live-pool execution agree with the snapshot. -/
namespace Keystone.KV

@[simp] theorem fillPage_size : (fillPage cache pageSize page entries).size = cache.size := by
  simp [fillPage]

/-- Filling a page leaves every other page unchanged. -/
theorem fillPage_other (hpage : 0 < pageSize) (hoffset : offset < pageSize)
    (hne : other ≠ page) :
    (fillPage cache pageSize page entries)[other * pageSize + offset]! =
      cache[other * pageSize + offset]! := by
  have hdiv : (other * pageSize + offset) / pageSize = other := by
    rw [Nat.mul_comm, Nat.mul_add_div hpage, Nat.div_eq_of_lt hoffset, Nat.add_zero]
  by_cases hb : other * pageSize + offset < cache.size
  · simp [fillPage, hb, hdiv, hne]
  · simp [fillPage, hb]

/-- A valid page write installs the supplied entries at that page's addresses. -/
theorem fillPage_at (hpage : 0 < pageSize) (hoffset : offset < pageSize)
    (hfits : page * pageSize + pageSize ≤ cache.size) :
    (fillPage cache pageSize page entries)[page * pageSize + offset]! = entries[offset]! := by
  have hb : page * pageSize + offset < cache.size := by omega
  have hdiv : (page * pageSize + offset) / pageSize = page := by
    rw [Nat.mul_comm, Nat.mul_add_div hpage, Nat.div_eq_of_lt hoffset, Nat.add_zero]
  have hmod : (page * pageSize + offset) % pageSize = offset := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hoffset]
  simp [fillPage, hb, hdiv, hmod]

/-- Live leases in a sufficiently large pool satisfy the GPU launch assumptions. -/
theorem ticket_validLaunch (hvalid : Valid s) (hpending : ticket ∈ s.pending)
    (hpage : 0 < cfg.pageSize) (hthreads : 0 < cfg.numThreads)
    (htokens : cfg.numTokens ≤ ticket.pages.length * cfg.pageSize)
    (hpool : s.capacity * cfg.pageSize ≤ cache.size) :
    GPU.ValidLaunch cfg (ticket.memory cache) := by
  refine ⟨hpage, hthreads, by simpa [Ticket.memory] using htokens, ?_⟩
  intro p
  have hp : p.val < ticket.pages.length := by simpa [Ticket.memory] using p.isLt
  have hl : ticket.pages[p.val] ∈ ticket.pages := List.getElem_mem hp
  have hb := hvalid.bounded _ (hvalid.protects ticket hpending _ hl)
  have hm := Nat.mul_le_mul_right cfg.pageSize (Nat.succ_le_of_lt hb)
  have he : GPU.physicalPage (ticket.memory cache) p = ticket.pages[p.val].page := by
    simp [GPU.physicalPage, Ticket.memory, hp]
  rw [he]
  simpa [Nat.add_mul, Ticket.memory] using Nat.le_trans hm hpool

/-- The live pool agrees with the launch snapshot on entries this gather can read. -/
def MemoryAgrees (cfg : GPU.Config) (snapshot current : GPU.KVMemory) : Prop :=
  current.pageTable = snapshot.pageTable ∧
  current.kvCache.size = snapshot.kvCache.size ∧
  ∀ t, t < cfg.numTokens → GPU.expectedEntry cfg current t = GPU.expectedEntry cfg snapshot t

/-- Keeping every captured page unchanged is enough; other pages may change. -/
theorem memoryAgrees_of_pages {ticket : Ticket} {snapshot current : Array UInt32}
    (hpage : 0 < cfg.pageSize)
    (htokens : cfg.numTokens ≤ ticket.pages.length * cfg.pageSize)
    (hsize : current.size = snapshot.size)
    (hcontents : ∀ lease ∈ ticket.pages, ∀ offset, offset < cfg.pageSize →
      current[lease.page * cfg.pageSize + offset]! =
        snapshot[lease.page * cfg.pageSize + offset]!) :
    MemoryAgrees cfg (ticket.memory snapshot) (ticket.memory current) := by
  refine ⟨rfl, hsize, ?_⟩
  intro t ht
  have hp : t / cfg.pageSize < ticket.pages.length :=
    (Nat.div_lt_iff_lt_mul hpage).mpr (Nat.lt_of_lt_of_le ht htokens)
  have hl : ticket.pages[t / cfg.pageSize] ∈ ticket.pages := List.getElem_mem hp
  simpa [GPU.expectedEntry, GPU.kvIndex, GPU.physicalPage, Ticket.memory, hp] using
    hcontents _ hl (t % cfg.pageSize) (Nat.mod_lt t hpage)

/-- A source step sees the same data even when unrelated shared pages change. -/
theorem source_step_eq (hinv : GPU.Invariant cfg snapshot kernel)
    (hagrees : MemoryAgrees cfg snapshot current) :
    GPU.step cfg current tid kernel = GPU.step cfg snapshot tid kernel := by
  obtain ⟨htable, hsize, hentries⟩ := hagrees
  by_cases ht : tid ≥ cfg.numThreads
  · simp [GPU.step, ht] <;> rfl
  · cases hp : (kernel.threads tid).instr with
    | load =>
      have hi := hinv.1 tid
      simp only [GPU.ThreadOK, hp] at hi
      have he := hentries _ hi.1
      have hindex : GPU.kvIndex cfg current (GPU.token cfg tid (kernel.threads tid).round) =
          (kernel.threads tid).kvIndex := by
        simp [GPU.kvIndex, GPU.physicalPage, htable, hi.2]
      have hindex' : GPU.kvIndex cfg snapshot (GPU.token cfg tid (kernel.threads tid).round) =
          (kernel.threads tid).kvIndex := by
        simpa [GPU.kvIndex, GPU.physicalPage] using hi.2.symm
      simp only [GPU.expectedEntry, hindex, hindex'] at he
      simp [GPU.step, ht, hp, hsize, he]
    | guard | page | table | kvIndex | store | done =>
      simp [GPU.step, ht, hp, GPU.physicalPage, htable]

/-- The actual compiled block reads the pool, with the snapshot's source semantics. -/
theorem compiled_step_eq (hinv : GPU.Invariant cfg snapshot kernel)
    (hagrees : MemoryAgrees cfg snapshot current) :
    Compile.step cfg current tid kernel = Compile.step cfg snapshot tid kernel := by
  rw [Compile.step_eq, Compile.step_eq, source_step_eq hinv hagrees]

/-- A live compiled step preserves the original gather invariant and cannot fault. -/
theorem compiled_step_safe (hvalid : GPU.ValidLaunch cfg snapshot)
    (hinv : GPU.Invariant cfg snapshot kernel)
    (hagrees : MemoryAgrees cfg snapshot current) (ht : tid < cfg.numThreads) :
    ∃ next accesses, Compile.step cfg current tid kernel = .ok (next, accesses) ∧
      GPU.Invariant cfg snapshot next := by
  obtain ⟨next, access, hstep, hnext⟩ := GPU.step_safe hvalid hinv ht
  refine ⟨next, access.toList, ?_, hnext⟩
  rw [compiled_step_eq hinv hagrees, Compile.step_eq, hstep]
  rfl

/-- A scheduled chunk against the live pool matches execution against its launch snapshot. -/
theorem compiled_run_eq (hvalid : GPU.ValidLaunch cfg snapshot)
    (hinv : GPU.Invariant cfg snapshot kernel)
    (hagrees : MemoryAgrees cfg snapshot current)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads) :
    Compile.run cfg current schedule kernel = Compile.run cfg snapshot schedule kernel := by
  induction schedule generalizing kernel with
  | nil => rfl
  | cons tid schedule ih =>
    have ht := hschedule tid (by simp)
    obtain ⟨next, accesses, hstep, hnext⟩ := compiled_step_safe hvalid hinv hagrees ht
    have hsnapshot : Compile.step cfg snapshot tid kernel = .ok (next, accesses) := by
      rw [← compiled_step_eq hinv hagrees]
      exact hstep
    simp only [Compile.run, hstep, hsnapshot]
    change (do let (last, more) ← Compile.run cfg current schedule next
               pure (last, accesses ++ more)) =
           (do let (last, more) ← Compile.run cfg snapshot schedule next
               pure (last, accesses ++ more))
    rw [ih hnext (fun t hm => hschedule t (by simp [hm]))]

end Keystone.KV

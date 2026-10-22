import Keystone.GPU.Progress
import Keystone.KV.Lifetime
import Keystone.Lowering.Gather

/-!
The controller supplies the gather's memory contract. This is a composition of
the two Lean models, not a refinement theorem for CUDA or a GPU driver.
The KV cache is an immutable array of complete physical pages; content stability
while a ticket is pending remains an obligation of the surrounding runtime.
-/
namespace Keystone

/-- The kernel's read-only memory for one pending ticket: its page snapshot as the page table. -/
def ticketMemory (ticket : KV.Ticket) (kvCache : Array UInt32) : GPU.KVMemory :=
  ⟨(ticket.pages.map KV.Lease.page).toArray, kvCache⟩

/-- An outstanding operation's ordered page snapshot satisfies the kernel's
physical bounds. Lease validity is derived from the controller invariant. -/
theorem pending_gather_contract (hs : KV.Valid s) (ht : ticket ∈ s.pending)
    (hpage : 0 < cfg.pageSize) (hlaunch : cfg.numTokens ≤ cfg.numThreads)
    (hcoverage : cfg.numTokens ≤ ticket.pages.length * cfg.pageSize)
    (hkvCache : kvCache.size = s.capacity * cfg.pageSize) :
    GPU.ValidLaunch cfg (ticketMemory ticket kvCache) := by
  refine ⟨hpage, hlaunch, ?_, ?_⟩
  · simpa [ticketMemory] using hcoverage
  · intro p
    have hm : GPU.physicalPage (ticketMemory ticket kvCache) p ∈
        (ticket.pages.map KV.Lease.page).toArray := by
      change (ticket.pages.map KV.Lease.page).toArray[p.val]! ∈ _
      rw [getElem!_pos (ticket.pages.map KV.Lease.page).toArray p.val p.isLt]
      exact Array.getElem_mem p.isLt
    obtain ⟨lease, hl, he⟩ := List.mem_map.mp (List.mem_toArray.mp hm)
    have hb := hs.bounded lease (hs.protects ticket ht lease hl)
    have hmul := Nat.mul_le_mul_right cfg.pageSize (Nat.succ_le_of_lt hb)
    rw [← he]
    change lease.page * cfg.pageSize + cfg.pageSize ≤ kvCache.size
    rw [hkvCache]
    simpa [Nat.add_mul] using hmul

/-- With a live ticket, the finite kernel runner completes safely and returns
the logical gather. The KV-cache content premise is visible in `ticketMemory`. -/
theorem pending_gather_correct (hs : KV.Valid s) (ht : ticket ∈ s.pending)
    (hpage : 0 < cfg.pageSize) (hlaunch : cfg.numTokens ≤ cfg.numThreads)
    (hcoverage : cfg.numTokens ≤ ticket.pages.length * cfg.pageSize)
    (hkvCache : kvCache.size = s.capacity * cfg.pageSize) :
    ∃ last accesses,
      GPU.run cfg (ticketMemory ticket kvCache) (GPU.roundRobin cfg) GPU.initialState =
        .ok (last, accesses) ∧
      GPU.completed cfg last = true ∧
      (∀ t, t < cfg.numTokens → last.output t =
        some (GPU.expectedEntry cfg (ticketMemory ticket kvCache) t)) ∧
      (∀ a ∈ accesses, GPU.AccessSafe cfg (ticketMemory ticket kvCache) a) := by
  exact GPU.verified_roundRobin
    (pending_gather_contract hs ht hpage hlaunch hcoverage hkvCache)

/-- Arbitrary host activity preserves both the captured leases and the gather
contract until this ticket completes. The same KV-cache array is deliberately an
explicit parameter: lease retention does not itself prove content stability. -/
theorem live_history_contract (hs : KV.Valid s) (ht : ticket ∈ s.pending)
    (hopen : KV.Action.complete ticket.id ∉ actions)
    (hpage : 0 < cfg.pageSize) (hlaunch : cfg.numTokens ≤ cfg.numThreads)
    (hcoverage : cfg.numTokens ≤ ticket.pages.length * cfg.pageSize)
    (hkvCache : kvCache.size = s.capacity * cfg.pageSize) :
    GPU.ValidLaunch cfg (ticketMemory ticket kvCache) ∧
    (∀ lease ∈ ticket.pages,
      lease ∈ (KV.run s actions).allocations ∧
      ∀ other ∈ (KV.run s actions).allocations, other.page = lease.page → other = lease) := by
  have hsize : kvCache.size = (KV.run s actions).capacity * cfg.pageSize := by
    simpa only [KV.run_capacity] using hkvCache
  have hnot : ∀ action ∈ actions, action ≠ KV.Action.complete ticket.id := by
    intro action ha he
    exact hopen (he ▸ ha)
  exact ⟨pending_gather_contract (KV.run_valid hs actions) (KV.pending_run ht hnot)
      hpage hlaunch hcoverage hsize,
    fun lease hl => KV.lifetime_safety hs ht hl hnot⟩

/-- A live KV snapshot supplies the memory premise of the verified lowering.
The extra word bounds make all mathematical indices representable. This
theorem stops at the flat target IR; native serialization is still trusted. -/
theorem pending_lowered_gather_correct (hs : KV.Valid s) (ht : ticket ∈ s.pending)
    (hpage : 0 < cfg.pageSize) (hlaunch : cfg.numTokens ≤ cfg.numThreads)
    (hcoverage : cfg.numTokens ≤ ticket.pages.length * cfg.pageSize)
    (hkvCache : kvCache.size = s.capacity * cfg.pageSize)
    (bounds : Lowering.NativeBounds cfg (ticketMemory ticket kvCache))
    (launched : tid < cfg.numThreads) (state : Lowering.State) :
    ∃ final, Lowering.target (Lowering.compile Lowering.gather)
        (Lowering.gatherContext cfg (ticketMemory ticket kvCache) tid)
        ⟨state, [], true, []⟩ = .ok ⟨final, [], true, []⟩ ∧
      final.output = (fun j => if tid < cfg.numTokens ∧ j = tid then
        GPU.expectedEntry cfg (ticketMemory ticket kvCache) tid else state.output j) ∧
      final.trace = state.trace ++ (if tid < cfg.numTokens then
        Lowering.gatherEvents cfg (ticketMemory ticket kvCache) tid else []) := by
  exact Lowering.gather_target_correct
    (pending_gather_contract hs ht hpage hlaunch hcoverage hkvCache) bounds launched state [] []

end Keystone

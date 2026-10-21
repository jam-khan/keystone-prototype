import Keystone.GPU.Progress
import Keystone.KV.Lifetime
import Keystone.Lowering.Gather

/-!
The controller supplies the gather's memory contract. This is a composition of
the two Lean models, not a refinement theorem for CUDA or a GPU driver.
The cache is an immutable array of complete physical pages; content stability
while a ticket is pending remains an obligation of the surrounding runtime.
-/
namespace Keystone

def ticketInput (ticket : KV.Ticket) (cache : Array UInt32) : GPU.Input :=
  ⟨(ticket.pages.map KV.Lease.page).toArray, cache⟩

/-- An outstanding operation's ordered page snapshot satisfies the kernel's
physical bounds. Lease validity is derived from the controller invariant. -/
theorem pending_gather_contract (hs : KV.Valid s) (ht : ticket ∈ s.pending)
    (hpage : 0 < cfg.pageSize) (hlaunch : cfg.n ≤ cfg.lanes)
    (hcoverage : cfg.n ≤ ticket.pages.length * cfg.pageSize)
    (hcache : cache.size = s.capacity * cfg.pageSize) :
    GPU.ValidInput cfg (ticketInput ticket cache) := by
  refine ⟨hpage, hlaunch, ?_, ?_⟩
  · simpa [ticketInput] using hcoverage
  · intro p
    have hm : GPU.physicalPage (ticketInput ticket cache) p ∈
        (ticket.pages.map KV.Lease.page).toArray := by
      change (ticket.pages.map KV.Lease.page).toArray[p.val]! ∈ _
      rw [getElem!_pos (ticket.pages.map KV.Lease.page).toArray p.val p.isLt]
      exact Array.getElem_mem p.isLt
    obtain ⟨lease, hl, he⟩ := List.mem_map.mp (List.mem_toArray.mp hm)
    have hb := hs.bounded lease (hs.protects ticket ht lease hl)
    have hmul := Nat.mul_le_mul_right cfg.pageSize (Nat.succ_le_of_lt hb)
    rw [← he]
    change lease.page * cfg.pageSize + cfg.pageSize ≤ cache.size
    rw [hcache]
    simpa [Nat.add_mul] using hmul

/-- With a live ticket, the finite kernel runner completes safely and returns
the logical gather. The cache-content premise is visible in `ticketInput`. -/
theorem pending_gather_correct (hs : KV.Valid s) (ht : ticket ∈ s.pending)
    (hpage : 0 < cfg.pageSize) (hlaunch : cfg.n ≤ cfg.lanes)
    (hcoverage : cfg.n ≤ ticket.pages.length * cfg.pageSize)
    (hcache : cache.size = s.capacity * cfg.pageSize) :
    ∃ last accesses,
      GPU.run cfg (ticketInput ticket cache) (GPU.roundRobin cfg) GPU.init =
        .ok (last, accesses) ∧
      GPU.completed cfg last = true ∧
      (∀ t, t < cfg.n → last.output t =
        some (GPU.referenceAt cfg (ticketInput ticket cache) t)) ∧
      (∀ a ∈ accesses, GPU.AccessSafe cfg (ticketInput ticket cache) a) := by
  exact GPU.verified_roundRobin
    (pending_gather_contract hs ht hpage hlaunch hcoverage hcache)

/-- Arbitrary host activity preserves both the captured leases and the gather
contract until this ticket completes. The same cache array is deliberately an
explicit parameter: lease retention does not itself prove content stability. -/
theorem live_history_contract (hs : KV.Valid s) (ht : ticket ∈ s.pending)
    (hopen : KV.Action.complete ticket.id ∉ actions)
    (hpage : 0 < cfg.pageSize) (hlaunch : cfg.n ≤ cfg.lanes)
    (hcoverage : cfg.n ≤ ticket.pages.length * cfg.pageSize)
    (hcache : cache.size = s.capacity * cfg.pageSize) :
    GPU.ValidInput cfg (ticketInput ticket cache) ∧
    (∀ lease ∈ ticket.pages,
      lease ∈ (KV.run s actions).allocations ∧
      ∀ other ∈ (KV.run s actions).allocations, other.page = lease.page → other = lease) := by
  have hsize : cache.size = (KV.run s actions).capacity * cfg.pageSize := by
    simpa only [KV.run_capacity] using hcache
  have hnot : ∀ action ∈ actions, action ≠ KV.Action.complete ticket.id := by
    intro action ha he
    exact hopen (he ▸ ha)
  exact ⟨pending_gather_contract (KV.run_valid hs actions) (KV.pending_run ht hnot)
      hpage hlaunch hcoverage hsize,
    fun lease hl => KV.lifetime_safety hs ht hl hnot⟩

/-- A live KV snapshot supplies the memory premise of the verified lowering.
The extra word bounds make all mathematical addresses representable. This
theorem stops at the flat target IR; native serialization is still trusted. -/
theorem pending_lowered_gather_correct (hs : KV.Valid s) (ht : ticket ∈ s.pending)
    (hpage : 0 < cfg.pageSize) (hlaunch : cfg.n ≤ cfg.lanes)
    (hcoverage : cfg.n ≤ ticket.pages.length * cfg.pageSize)
    (hcache : cache.size = s.capacity * cfg.pageSize)
    (bounds : Lowering.NativeBounds cfg (ticketInput ticket cache))
    (launched : tid < cfg.lanes) (state : Lowering.State) :
    ∃ final, Lowering.target (Lowering.compile Lowering.gather)
        (Lowering.gatherContext cfg (ticketInput ticket cache) tid)
        ⟨state, [], true, []⟩ = .ok ⟨final, [], true, []⟩ ∧
      final.output = (fun j => if tid < cfg.n ∧ j = tid then
        GPU.referenceAt cfg (ticketInput ticket cache) tid else state.output j) ∧
      final.trace = state.trace ++ (if tid < cfg.n then
        Lowering.gatherEvents cfg (ticketInput ticket cache) tid else []) := by
  exact Lowering.gather_target_correct
    (pending_gather_contract hs ht hpage hlaunch hcoverage hcache) bounds launched state [] []

end Keystone

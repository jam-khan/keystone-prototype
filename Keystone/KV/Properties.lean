import Keystone.GPU.KVGather -- Source execution and expected gather output.
import Keystone.GPU.Properties -- run_safe and AccessSafe.
import Keystone.Compile.Compiler -- Compile.run executes the live-pool chunk.
import Keystone.Compile.Correctness -- run_eq connects compiled and source runs.
import Keystone.KV.Manager -- Leases, tickets, manager validity, and histories.
import Keystone.KV.Runtime -- Connected allocation, execution, and completion.
import Keystone.KV.Proofs.Manager -- Lease retention and manager preservation.
import Keystone.KV.Proofs.Memory -- compiled_run_eq for live versus snapshot memory.
import Keystone.KV.Proofs.Runtime -- Runtime.Valid and supporting invariant proofs.

/-!
Main guarantees: retain pages until completion, reclaim retired pages after their last use,
execute the proved GPU model, and return its expected output. Supporting proofs are in Proofs/.
-/
namespace Keystone.KV

-- Page lifetime.

/-- Until completion, every captured lease remains allocated and exclusive. -/
theorem lifetime_safety (h : Valid s) (ht : ticket ∈ s.pending)
    (hl : lease ∈ ticket.pages)
    (notCompleted : ∀ action ∈ actions, action ≠ .complete ticket.id) :
    lease ∈ (run s actions).allocations ∧
      ∀ other ∈ (run s actions).allocations, other.page = lease.page → other = lease := by
  have finalValid := run_valid h actions
  have stillPending := pending_run ht notCompleted
  exact ⟨finalValid.protects ticket stillPending lease hl,
    fun other ho eq => pending_cannot_reassign finalValid stillPending hl ho eq⟩

/-- The final completion reclaims retired pages; no device liveness is assumed. -/
theorem reclaim_after_last_completion (id : Nat)
    (retired : lease.owner ∈ s.retired)
    (finishing : ∃ ticket ∈ s.pending, ticket.id = id)
    (lastUse : ∀ ticket ∈ s.pending, lease ∈ ticket.pages → ticket.id = id) :
    lease ∉ (complete s id).allocations := by
  simp only [complete, ite_eq_left finishing]
  intro hm
  have live := (mem_collect.mp hm).2
  rcases live with active | ⟨ticket, ht, hl⟩
  · exact active retired
  · have ht' := List.mem_filter.mp ht
    have neq : ticket.id ≠ id := by simpa using ht'.2
    exact neq (lastUse ticket ht'.1 hl)

-- Execution through Compile.run. Runtime.Valid is defined in Proofs/Runtime.lean.

namespace Runtime

variable {id : Nat}

/-- Each runtime chunk has the full state and trace of the original GPU semantics. -/
theorem run_eq_source (h : Valid r) (hjob : r.jobs id = some job)
    (hschedule : ∀ tid ∈ schedule, tid < job.config.numThreads) :
    run r id schedule = (do
      let (kernel, accesses) ←
        (GPU.run job.config job.memory schedule job.kernel).mapError Fault.gpu
      pure (withJob r id (some { job with kernel }), accesses)) := by
  have hj := (h.jobs id job hjob).2
  have he := compiled_run_eq hj.launch hj.invariant hj.agrees hschedule
  simp only [run, hjob]
  change (do
    let (kernel, accesses) ←
      (Compile.run job.config (job.ticket.memory r.cache) schedule job.kernel).mapError Fault.gpu
    pure (withJob r id (some { job with kernel }), accesses)) = _
  rw [he, Compile.run_eq]

/-- Every valid scheduled chunk succeeds, and its accesses stay inside the live buffers. -/
theorem run_safe (h : Valid r) (hjob : r.jobs id = some job)
    (hschedule : ∀ tid ∈ schedule, tid < job.config.numThreads) :
    ∃ next accesses, run r id schedule = .ok (next, accesses) ∧ Valid next ∧
      ∀ access ∈ accesses, GPU.AccessSafe job.config (job.ticket.memory r.cache) access := by
  have hj := (h.jobs id job hjob).2
  obtain ⟨kernel, accesses, hr, hi, ha⟩ := GPU.run_safe hj.launch hj.invariant hschedule
  refine ⟨withJob r id (some { job with kernel }), accesses, ?_,
    withKernel_valid h hjob hi, ?_⟩
  · rw [run_eq_source h hjob hschedule, hr]
    rfl
  · intro access hm
    have hb := ha access hm
    cases access.buffer <;>
      simpa [GPU.AccessSafe, Job.memory, Ticket.memory, hj.size] using hb

/-- Successful execution preserves the runtime invariant. -/
theorem run_valid (h : Valid r) (hjob : r.jobs id = some job)
    (hschedule : ∀ tid ∈ schedule, tid < job.config.numThreads)
    (hok : run r id schedule = .ok (next, accesses)) : Valid next := by
  obtain ⟨result, trace, hr, hv, _⟩ := run_safe h hjob hschedule
  cases Except.ok.inj (hr.symm.trans hok)
  exact hv

/-- Completion returns the gather's expected output from the launch snapshot. -/
theorem finish_correct (h : Valid r) (hjob : r.jobs id = some job)
    (hok : finish r id = some (next, output)) :
    output = (GPU.expectedOutput job.config job.memory).map some := by
  obtain ⟨finished, found, done, rfl⟩ := finish_requires_completed hok
  have same : finished = job := Option.some.inj (found.symm.trans hjob)
  subst finished
  exact completed_output (h.jobs id job hjob).2 done

end Runtime
end Keystone.KV

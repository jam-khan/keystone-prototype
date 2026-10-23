import Keystone.GPU.KVGather -- GPU launch, memory, state, and completion.
import Keystone.GPU.Auxiliary -- Invariant, initial_invariant, and finished_correct.
import Keystone.GPU.Properties -- completed_eq_true.
import Keystone.KV.Manager -- Manager state and page-lifetime operations.
import Keystone.KV.Runtime -- Shared pool and connected kernel operations.
import Keystone.KV.Proofs.Manager -- Manager preservation and complete_pending.
import Keystone.KV.Proofs.Memory -- Page writes, launch conditions, and memory agreement.

/-! Invariants and supporting proofs for the guarantees in KV/Properties.lean. -/
namespace Keystone.KV.Runtime

/-- Each job retains its pages, original contents, and the GPU proof invariant. -/
structure JobValid (r : Runtime) (job : Job) : Prop where
  pageSize : job.config.pageSize = r.pageSize
  pending : job.ticket ∈ r.manager.pending
  launch : GPU.ValidLaunch job.config job.memory
  invariant : GPU.Invariant job.config job.memory job.kernel
  size : r.cache.size = job.snapshot.size
  contents : ∀ lease ∈ job.ticket.pages, ∀ offset, offset < r.pageSize →
    r.cache[lease.page * r.pageSize + offset]! =
      job.snapshot[lease.page * r.pageSize + offset]!

/-- Pending tickets and running kernels correspond; the shared pool respects every job. -/
structure Valid (r : Runtime) : Prop where
  manager : KV.Valid r.manager
  pageSize : 0 < r.pageSize
  capacity : r.manager.capacity * r.pageSize = r.cache.size
  jobs : ∀ id job, r.jobs id = some job → job.ticket.id = id ∧ JobValid r job
  pending : ∀ ticket ∈ r.manager.pending,
    ∃ job, r.jobs ticket.id = some job ∧ job.ticket = ticket

variable {r next : Runtime} {id owner numTokens numThreads capacity pageSize : Nat}

-- Host operations preserve the manager and every pending job.

theorem init_valid (hpage : 0 < pageSize) : Valid (init capacity pageSize) := by
  refine ⟨KV.init_valid capacity, hpage, ?_, ?_, ?_⟩
  · simp [init, KV.init]
  · simp [init]
  · simp [init, KV.init]

/-- Filling a newly allocated page preserves every pending gather's captured contents. -/
theorem allocate_valid (h : Valid r)
    (ok : allocate r owner entries = some (next, lease)) : Valid next := by
  unfold allocate at ok
  split at ok
  · contradiction
  · cases found : KV.allocate r.manager owner with
    | none => simp [found] at ok
    | some pair =>
      simp [found] at ok
      obtain ⟨rfl, rfl⟩ := ok
      obtain ⟨hm, _, _, _, hfree⟩ := KV.allocate_success found
      have manager := KV.allocate_valid h.manager found
      rw [hm] at manager ⊢
      refine ⟨manager, h.pageSize, ?_, ?_, ?_⟩
      · simpa using h.capacity
      · intro id job hj
        obtain ⟨hid, jv⟩ := h.jobs id job hj
        refine ⟨hid, jv.pageSize, jv.pending, jv.launch, jv.invariant, ?_, ?_⟩
        · simpa using jv.size
        · intro old hold offset hoff
          rw [fillPage_other h.pageSize hoff
            (hfree old (h.manager.protects job.ticket jv.pending old hold))]
          exact jv.contents old hold offset hoff
      · exact h.pending

/-- Starting a gather captures the pool and uses its leases as the actual GPU page table. -/
theorem launch_valid (h : Valid r)
    (ok : launch r owner pages numTokens numThreads = some (next, id)) : Valid next := by
  unfold launch at ok
  split at ok
  · contradiction
  · rename_i allowed
    have dimensions : 0 < r.pageSize ∧ 0 < numThreads ∧
        numTokens ≤ pages.length * r.pageSize := by simpa using allowed
    cases found : submit r.manager owner pages with
    | none => simp [found] at ok
    | some pair =>
      simp [found] at ok
      obtain ⟨rfl, rfl⟩ := ok
      obtain ⟨hm, ht, _, _⟩ := submit_success found
      have manager := submit_valid h.manager found
      have captured : pair.2 ∈ pair.1.pending := by simp [hm]
      have launch : GPU.ValidLaunch ⟨numTokens, r.pageSize, numThreads⟩
          (pair.2.memory r.cache) :=
        ticket_validLaunch manager captured dimensions.1 dimensions.2.1
          (by simpa [ht] using dimensions.2.2) (by simpa [hm] using Nat.le_of_eq h.capacity)
      refine ⟨manager, h.pageSize, ?_, ?_, ?_⟩
      · simpa [withJob, hm] using h.capacity
      · intro key job hj
        by_cases he : key = pair.2.id
        · simp [withJob, he] at hj
          subst job
          refine ⟨he.symm, rfl, captured, launch, GPU.initial_invariant, rfl, ?_⟩
          intro _ _ _ _; rfl
        · have old : r.jobs key = some job := by simpa [withJob, he] using hj
          obtain ⟨hid, jv⟩ := h.jobs key job old
          refine ⟨hid, jv.pageSize, ?_, jv.launch, jv.invariant, jv.size, jv.contents⟩
          simp [withJob, hm, jv.pending]
      · intro ticket hp
        change ticket ∈ pair.1.pending at hp
        rw [hm] at hp
        rcases List.mem_cons.mp hp with rfl | hp
        · refine ⟨⟨pair.2, ⟨numTokens, r.pageSize, numThreads⟩, r.cache, GPU.initialState⟩, ?_, rfl⟩
          simp [withJob]
        · obtain ⟨job, hj, hjt⟩ := h.pending ticket hp
          have hne : ticket.id ≠ pair.2.id := by
            have hb := h.manager.tickets ticket hp
            simp only [ht] at *
            omega
          exact ⟨job, by simpa [withJob, hne] using hj, hjt⟩

/-- Cancelling a request preserves its pending kernels and their memory. -/
theorem cancel_valid (h : Valid r) : Valid (cancel r owner) := by
  refine ⟨retire_valid h.manager, h.pageSize, h.capacity, ?_, h.pending⟩
  intro id job hj
  obtain ⟨hid, jv⟩ := h.jobs id job hj
  exact ⟨hid, jv.pageSize, jv.pending, jv.launch, jv.invariant, jv.size, jv.contents⟩

/-- Returning from `finish` requires the existing GPU model's completion check. -/
theorem finish_requires_completed (ok : finish r id = some (next, output)) :
    ∃ job, r.jobs id = some job ∧ GPU.completed job.config job.kernel = true ∧
      output = GPU.outputEntries job.config job.kernel := by
  unfold finish at ok
  cases hj : r.jobs id with
  | none => simp [hj] at ok
  | some job =>
    simp [hj] at ok
    obtain ⟨done, rfl, rfl⟩ := ok
    exact ⟨job, rfl, by simpa using done, rfl⟩

/-- Removing a completed job releases exactly its ticket; other jobs stay valid. -/
theorem finish_valid (h : Valid r)
    (ok : finish r id = some (next, output)) : Valid next := by
  unfold finish at ok
  cases hj : r.jobs id with
  | none => simp [hj] at ok
  | some job =>
    simp [hj] at ok
    obtain ⟨_, rfl, rfl⟩ := ok
    refine ⟨complete_valid id h.manager, h.pageSize, ?_, ?_, ?_⟩
    · change (complete r.manager id).capacity * r.pageSize = r.cache.size
      unfold complete
      split <;> exact h.capacity
    · intro key other ho
      by_cases he : key = id
      · simp [withJob, he] at ho
      · have old : r.jobs key = some other := by simpa [withJob, he] using ho
        obtain ⟨hid, jv⟩ := h.jobs key other old
        refine ⟨hid, jv.pageSize, ?_, jv.launch, jv.invariant, jv.size, jv.contents⟩
        exact (complete_pending id).mpr ⟨jv.pending, by simpa [hid] using he⟩
    · intro ticket hp
      have hp' := (complete_pending id).mp hp
      obtain ⟨other, ho, ht⟩ := h.pending ticket hp'.1
      exact ⟨other, by simpa [withJob, hp'.2] using ho, ht⟩

-- Execution preserves the captured contents and GPU invariant.

/-- Retained page contents give exactly the memory agreement needed by the compiler bridge. -/
theorem JobValid.agrees (h : JobValid r job) :
    MemoryAgrees job.config job.memory (job.ticket.memory r.cache) := by
  apply memoryAgrees_of_pages h.launch.1
  · simpa [Job.memory, Ticket.memory] using h.launch.2.2.1
  · exact h.size
  · simpa only [h.pageSize] using h.contents

private theorem jobValid_withJob (h : JobValid r job) : JobValid (withJob r id replacement) job :=
  ⟨h.pageSize, h.pending, h.launch, h.invariant, h.size, h.contents⟩

theorem withKernel_valid (h : Valid r) (hjob : r.jobs id = some job)
    (hinv : GPU.Invariant job.config job.memory kernel) :
    Valid (withJob r id (some { job with kernel })) := by
  have hj := h.jobs id job hjob
  refine ⟨h.manager, h.pageSize, h.capacity, ?_, ?_⟩
  · intro j other ho
    by_cases he : j = id
    · subst j
      simp [withJob] at ho
      subst other
      exact ⟨hj.1, jobValid_withJob ⟨hj.2.pageSize, hj.2.pending, hj.2.launch,
        hinv, hj.2.size, hj.2.contents⟩⟩
    · have hold : r.jobs j = some other := by simpa [withJob, he] using ho
      exact ⟨(h.jobs j other hold).1, jobValid_withJob (h.jobs j other hold).2⟩
  · intro ticket ht
    obtain ⟨other, ho, he⟩ := h.pending ticket ht
    by_cases hid : ticket.id = id
    · have ho' : some job = some other := hjob.symm.trans (hid ▸ ho)
      cases ho'
      exact ⟨{ job with kernel }, by simp [withJob, hid], he⟩
    · exact ⟨other, by simpa [withJob, hid] using ho, he⟩

/-- A finished job has the gather result from submission, despite other pool allocations. -/
theorem completed_output (h : JobValid r job)
    (hdone : GPU.completed job.config job.kernel = true) :
    GPU.outputEntries job.config job.kernel =
      (GPU.expectedOutput job.config job.memory).map some := by
  apply Array.ext
  · simp [GPU.outputEntries, GPU.expectedOutput]
  · intro i hi _
    have hb : i < job.config.numTokens := by simpa [GPU.outputEntries] using hi
    simpa [GPU.outputEntries, GPU.expectedOutput] using
      GPU.finished_correct h.launch h.invariant (GPU.completed_eq_true.mp hdone) hb

end Keystone.KV.Runtime

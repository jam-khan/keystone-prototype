import Keystone.GPU.Model

namespace Keystone.GPU

/-- A real thread's `.table` read is inside the page table. -/
theorem table_bounds
  (h : ValidInput cfg input)
  (ht : tid < cfg.numElements)
    : tid / cfg.pageSize < input.pageTable.size := by
  unfold ValidInput at h
  -- h : 0 < pageSize ∧ numElements ≤ numThreads ∧ numElements ≤ pageTable.size * pageSize ∧ ∀ p, …
  -- name the four conjuncts in order (`_` prefix = unused here)
  obtain ⟨hpos, _hthreads, hcapacity, _hpages⟩ := h
  -- numElements ≤ pageTable.size * pageSize, so tid < pageTable.size * pageSize
  have h1 : tid < input.pageTable.size * cfg.pageSize := Nat.lt_of_lt_of_le ht hcapacity
  -- divide both sides by pageSize (> 0)
  exact (Nat.div_lt_iff_lt_mul hpos).mpr h1

/-- A real thread's `.load` read is inside the KV cache. -/
theorem kvCache_bounds
  (h : ValidInput cfg input)
  (ht : tid < cfg.numElements)
    : kvIndex cfg input tid < input.kvCache.size := by
  unfold kvIndex
  -- unfold physicalPage
  -- unfold ValidInput at h
  have h' := table_bounds h ht
  obtain ⟨hpos, _hthreads, hcapacity, hpages⟩ := h
  have hfits := hpages ⟨tid / cfg.pageSize, h'⟩
  have hoffset : tid % cfg.pageSize < cfg.pageSize := by
    exact Nat.mod_lt tid hpos
  simp at hfits
  have hstep := Nat.add_lt_add_left hoffset (physicalPage input (tid / cfg.pageSize) * cfg.pageSize)
  exact Nat.lt_of_lt_of_le hstep hfits

/-! ## Invariant: what is true of every thread between steps -/

/--
  `ThreadOK` is a predicate to ensure an invariant for a thread during
  steps. So, essentially, it states the properties a thread would hold
  under which `instr` instruction set
-/
def ThreadOK (cfg : Config) (input : Input) (tid : Nat) (thread : Thread) : Prop :=
  match thread.instr with
  | .guard | .done => True
  | .page    => tid < cfg.numElements
  | .table   => tid < cfg.numElements ∧ thread.page     = tid / cfg.pageSize
  | .kvIndex => tid < cfg.numElements ∧ thread.physical = physicalPage input (tid / cfg.pageSize)
  | .load    => tid < cfg.numElements ∧ thread.kvIndex  = kvIndex cfg input tid
  | .store   => tid < cfg.numElements ∧ thread.value    = expectedValue cfg input tid

/--
  Every thread is OK, and output slot `tid` is filled exactly when
  real thread `tid` has finished, with the expected value.
-/
def Invariant (cfg : Config) (input : Input) (m : Machine) : Prop :=
  ∀ tid, ThreadOK cfg input tid (m.threads tid) ∧
    m.output tid = if tid < cfg.numElements ∧ (m.threads tid).instr = .done
      then some (expectedValue cfg input tid) else none

-- the initial machine satisfies the invariant: every thread at `.guard`, no outputs
@[simp] theorem initial_invariant : Invariant cfg input init := by
  intro tid
  simp [ThreadOK, init]

-- replacing one thread's state keeps the invariant, if the new state is OK
private theorem withThread_invariant (h : Invariant cfg input m)
    (hthread : ThreadOK cfg input tid thread)
    (houtput : m.output tid = if tid < cfg.numElements ∧ thread.instr = .done
      then some (expectedValue cfg input tid) else none) :
    Invariant cfg input (withThread m tid thread) := by
  intro j
  by_cases hj : j = tid
  · subst j
    simpa [withThread] using And.intro hthread houtput
  · simpa [withThread, hj] using h j

-- `.store` keeps the invariant: thread finishes and writes the expected value
private theorem store_invariant (h : Invariant cfg input m)
    (ht : tid < cfg.numElements) (hv : value = expectedValue cfg input tid) :
    Invariant cfg input
      (withOutput (withThread m tid { m.threads tid with instr := .done }) tid value) := by
  intro j
  by_cases hj : j = tid
  · subst j
    simp [withOutput, withThread, ThreadOK, ht, hv]
  · simpa [withOutput, withThread, hj] using h j

/-! ## Safety: no step faults, every access is in bounds -/

/-- An access is by a real thread, in bounds, and stores go to the thread's own slot. -/
def AccessSafe (cfg : Config) (input : Input) (a : Access) : Prop :=
  a.thread < cfg.numThreads ∧ a.thread < cfg.numElements ∧ match a.buffer with
    | .pageTable => a.index < input.pageTable.size
    | .kvCache   => a.index < input.kvCache.size
    | .output    => a.index = a.thread ∧ a.index < cfg.numElements

-- a step makes either no access, or a safe one
def EventSafe (cfg : Config) (input : Input) : Option Access → Prop
  | none => True
  | some a => AccessSafe cfg input a

/-- A launched thread steps without faulting, keeps the invariant, and accesses safely. -/
theorem step_safe (hvalid : ValidInput cfg input) (hinv : Invariant cfg input m)
    (ht : tid < cfg.numThreads) :
    ∃ next access, step cfg input tid m = .ok (next, access) ∧
      Invariant cfg input next ∧ EventSafe cfg input access := by
  have hi := (hinv tid).1
  have ho := (hinv tid).2
  -- one case per instruction
  cases hp : (m.threads tid).instr with
  | guard =>
    by_cases hn : tid < cfg.numElements
    · -- real thread: go to `.page`
      refine ⟨withThread m tid { m.threads tid with instr := .page }, none, ?_, ?_, trivial⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · apply withThread_invariant hinv
        · simpa [ThreadOK] using hn
        · simpa [hp, hn] using ho
    · -- padded thread: go to `.done`
      refine ⟨withThread m tid { m.threads tid with instr := .done }, none, ?_, ?_, trivial⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · apply withThread_invariant hinv
        · trivial
        · simpa [hp, hn] using ho
  | page =>
    have hn : tid < cfg.numElements := by simpa [ThreadOK, hp] using hi
    refine ⟨withThread m tid { m.threads tid with instr := .table, page := tid / cfg.pageSize },
      none, ?_, ?_, trivial⟩
    · simp [step, Nat.not_le_of_gt ht, hp] <;> rfl
    · apply withThread_invariant hinv
      · exact ⟨hn, rfl⟩
      · simpa [hp] using ho
  | table =>
    have hi' : tid < cfg.numElements ∧ (m.threads tid).page = tid / cfg.pageSize := by
      simpa [ThreadOK, hp] using hi
    -- the page-table read is in bounds (table_bounds)
    have hb : (m.threads tid).page < input.pageTable.size := by
      rw [hi'.2]; exact table_bounds hvalid hi'.1
    refine ⟨withThread m tid { m.threads tid with
        instr := .kvIndex, physical := physicalPage input (m.threads tid).page },
      some ⟨tid, .pageTable, (m.threads tid).page⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hb] <;> rfl
    · apply withThread_invariant hinv
      · exact ⟨hi'.1, congrArg (physicalPage input) hi'.2⟩
      · simpa [hp] using ho
    · exact ⟨ht, hi'.1, hb⟩
  | kvIndex =>
    have hi' : tid < cfg.numElements ∧
        (m.threads tid).physical = physicalPage input (tid / cfg.pageSize) := by
      simpa [ThreadOK, hp] using hi
    refine ⟨withThread m tid { m.threads tid with
        instr := .load, kvIndex := (m.threads tid).physical * cfg.pageSize + tid % cfg.pageSize },
      none, ?_, ?_, trivial⟩
    · simp [step, Nat.not_le_of_gt ht, hp] <;> rfl
    · apply withThread_invariant hinv
      · constructor
        · exact hi'.1
        · simp [kvIndex, hi'.2]
      · simpa [hp] using ho
  | load =>
    have hi' : tid < cfg.numElements ∧ (m.threads tid).kvIndex = kvIndex cfg input tid := by
      simpa [ThreadOK, hp] using hi
    -- the KV-cache read is in bounds (kvCache_bounds)
    have hb : (m.threads tid).kvIndex < input.kvCache.size := by
      rw [hi'.2]; exact kvCache_bounds hvalid hi'.1
    refine ⟨withThread m tid { m.threads tid with
        instr := .store, value := input.kvCache[(m.threads tid).kvIndex]! },
      some ⟨tid, .kvCache, (m.threads tid).kvIndex⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hb] <;> rfl
    · apply withThread_invariant hinv
      · exact ⟨hi'.1, congrArg (fun a => input.kvCache[a]!) hi'.2⟩
      · simpa [hp] using ho
    · exact ⟨ht, hi'.1, hb⟩
  | store =>
    have hi' : tid < cfg.numElements ∧ (m.threads tid).value = expectedValue cfg input tid := by
      simpa [ThreadOK, hp] using hi
    -- the output write goes to slot `tid`, in bounds because tid < numElements
    refine ⟨withOutput (withThread m tid { m.threads tid with instr := .done }) tid (m.threads tid).value,
      some ⟨tid, .output, tid⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hi'.1] <;> rfl
    · exact store_invariant hinv hi'.1 hi'.2
    · exact ⟨ht, hi'.1, rfl, hi'.1⟩
  | done =>
    exact ⟨m, none, by simp [step, Nat.not_le_of_gt ht, hp] <;> rfl, hinv, trivial⟩

/-- Any schedule of launched threads runs without faults; it need not finish. -/
theorem run_safe (hvalid : ValidInput cfg input) (hinv : Invariant cfg input m)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads) :
    ∃ last accesses, run cfg input schedule m = .ok (last, accesses) ∧
      Invariant cfg input last ∧ ∀ a ∈ accesses, AccessSafe cfg input a := by
  induction schedule generalizing m with
  | nil => exact ⟨m, [], rfl, hinv, by simp⟩
  | cons tid schedule ih =>
    -- first step is safe (step_safe), the rest by induction
    obtain ⟨next, access, hstep, hnext, ha⟩ :=
      step_safe hvalid hinv (hschedule tid (by simp))
    obtain ⟨last, accesses, hrun, hlast, has⟩ :=
      ih hnext (fun j hj => hschedule j (by simp [hj]))
    refine ⟨last, access.toList ++ accesses, ?_, hlast, ?_⟩
    · simp only [run, hstep]
      change (do let (last, accesses) ← run cfg input schedule next
                 pure (last, access.toList ++ accesses)) = _
      rw [hrun]
      rfl
    · intro a ha'
      rcases List.mem_append.mp ha' with hleft | hright
      · cases access with
        | none => simp at hleft
        | some b =>
          have hab : a = b := by simpa using hleft
          subst a
          exact ha
      · exact has a hright

/-! ## Correctness: a finished run produces the expected output -/

def Finished (cfg : Config) (m : Machine) : Prop :=
  ∀ tid, tid < cfg.numThreads → (m.threads tid).instr = .done

@[simp] theorem completed_eq_true : completed cfg m = true ↔ Finished cfg m := by
  simp [completed, Finished, List.all_eq_true]

-- once every thread is done, the invariant says each output slot holds the expected value
theorem finished_correct (hvalid : ValidInput cfg input)
    (hinv : Invariant cfg input m) (hfinished : Finished cfg m)
    (ht : tid < cfg.numElements) : m.output tid = some (expectedValue cfg input tid) := by
  have hd := hfinished tid (Nat.lt_of_lt_of_le ht hvalid.2.1)
  simpa [ht, hd] using (hinv tid).2

/-- For ANY schedule that finishes: output matches the spec, and every access was safe. -/
theorem completed_execution_correct (hvalid : ValidInput cfg input)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads)
    (hrun : run cfg input schedule init = .ok (last, accesses))
    (hdone : completed cfg last = true) :
    (∀ tid, tid < cfg.numElements → last.output tid = some (expectedValue cfg input tid)) ∧
    (∀ a ∈ accesses, AccessSafe cfg input a) := by
  obtain ⟨last', accesses', hr, hi, ha⟩ := run_safe hvalid initial_invariant hschedule
  rw [hrun] at hr
  cases hr
  exact ⟨fun _ ht => finished_correct hvalid hi (completed_eq_true.mp hdone) ht, ha⟩

/-- Padded threads make no memory accesses. -/
theorem padded_threads_no_access (h : AccessSafe cfg input a) : a.thread < cfg.numElements :=
  h.2.1

/-- Two different threads never write the same output slot. -/
theorem distinct_threads_disjoint_stores (ha : AccessSafe cfg input a)
    (hb : AccessSafe cfg input b) (hsa : a.buffer = .output) (hsb : b.buffer = .output)
    (hne : a.thread ≠ b.thread) : a.index ≠ b.index := by
  have hae : a.index = a.thread := by
    have h := ha.2.2
    rw [hsa] at h
    exact h.1
  have hbe : b.index = b.thread := by
    have h := hb.2.2
    rw [hsb] at h
    exact h.1
  simpa [hae, hbe] using hne

end Keystone.GPU

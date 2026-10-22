import Keystone.GPU.KVGather

namespace Keystone.GPU

/-- A real thread's `.table` read is inside the page table. -/
theorem table_bounds
  (h : ValidLaunch cfg mem)
  (ht : tid < cfg.numTokens)
    : tid / cfg.pageSize < mem.pageTable.size := by
  unfold ValidLaunch at h
  -- h : 0 < pageSize ∧ numTokens ≤ numThreads ∧ numTokens ≤ pageTable.size * pageSize ∧ ∀ p, …
  -- name the four conjuncts in order (`_` prefix = unused here)
  obtain ⟨hpos, _hthreads, hcapacity, _hpages⟩ := h
  -- numTokens ≤ pageTable.size * pageSize, so tid < pageTable.size * pageSize
  have h1 : tid < mem.pageTable.size * cfg.pageSize := Nat.lt_of_lt_of_le ht hcapacity
  -- divide both sides by pageSize (> 0)
  exact (Nat.div_lt_iff_lt_mul hpos).mpr h1

/-- A real thread's `.load` read is inside the KV cache. -/
theorem kvCache_bounds
  (h : ValidLaunch cfg mem)
  (ht : tid < cfg.numTokens)
    : kvIndex cfg mem tid < mem.kvCache.size := by
  unfold kvIndex
  -- unfold physicalPage
  -- unfold ValidLaunch at h
  have h' := table_bounds h ht
  obtain ⟨hpos, _hthreads, hcapacity, hpages⟩ := h
  have hfits := hpages ⟨tid / cfg.pageSize, h'⟩
  have hoffset : tid % cfg.pageSize < cfg.pageSize := by
    exact Nat.mod_lt tid hpos
  simp at hfits
  have hstep := Nat.add_lt_add_left hoffset (physicalPage mem (tid / cfg.pageSize) * cfg.pageSize)
  exact Nat.lt_of_lt_of_le hstep hfits

/-! ## Invariant: what is true of every thread between steps -/

/--
  `ThreadOK` is a predicate to ensure an invariant for a thread during
  steps. So, essentially, it states the properties a thread would hold
  under which `instr` instruction set
-/
def ThreadOK (cfg : Config) (mem : KVMemory) (tid : Nat) (thread : Thread) : Prop :=
  match thread.instr with
  | .guard | .done => True
  | .page    => tid < cfg.numTokens
  | .table   => tid < cfg.numTokens ∧ thread.logicalPage  = tid / cfg.pageSize
  | .kvIndex => tid < cfg.numTokens ∧ thread.physicalPage = physicalPage mem (tid / cfg.pageSize)
  | .load    => tid < cfg.numTokens ∧ thread.kvIndex      = kvIndex cfg mem tid
  | .store   => tid < cfg.numTokens ∧ thread.entry        = expectedEntry cfg mem tid

/--
  Every thread is OK, and output slot `tid` is filled exactly when
  real thread `tid` has finished, with the expected entry.
-/
def Invariant (cfg : Config) (mem : KVMemory) (s : KernelState) : Prop :=
  ∀ tid, ThreadOK cfg mem tid (s.threads tid) ∧
    s.output tid = if tid < cfg.numTokens ∧ (s.threads tid).instr = .done
      then some (expectedEntry cfg mem tid) else none

-- the initial state satisfies the invariant: every thread at `.guard`, no outputs
@[simp] theorem initial_invariant : Invariant cfg mem initialState := by
  intro tid
  simp [ThreadOK, initialState]

-- replacing one thread's state keeps the invariant, if the new state is OK
private theorem withThread_invariant (h : Invariant cfg mem s)
    (hthread : ThreadOK cfg mem tid thread)
    (houtput : s.output tid = if tid < cfg.numTokens ∧ thread.instr = .done
      then some (expectedEntry cfg mem tid) else none) :
    Invariant cfg mem (withThread s tid thread) := by
  intro j
  by_cases hj : j = tid
  · subst j
    simpa [withThread] using And.intro hthread houtput
  · simpa [withThread, hj] using h j

-- `.store` keeps the invariant: thread finishes and writes the expected entry
private theorem store_invariant (h : Invariant cfg mem s)
    (ht : tid < cfg.numTokens) (hv : entry = expectedEntry cfg mem tid) :
    Invariant cfg mem
      (withOutput (withThread s tid { s.threads tid with instr := .done }) tid entry) := by
  intro j
  by_cases hj : j = tid
  · subst j
    simp [withOutput, withThread, ThreadOK, ht, hv]
  · simpa [withOutput, withThread, hj] using h j

/-! ## Safety: no step faults, every access is in bounds -/

/-- An access is by a real thread, in bounds, and stores go to the thread's own slot. -/
def AccessSafe (cfg : Config) (mem : KVMemory) (a : Access) : Prop :=
  a.thread < cfg.numThreads ∧ a.thread < cfg.numTokens ∧ match a.buffer with
    | .pageTable => a.index < mem.pageTable.size
    | .kvCache   => a.index < mem.kvCache.size
    | .output    => a.index = a.thread ∧ a.index < cfg.numTokens

-- a step makes either no access, or a safe one
def EventSafe (cfg : Config) (mem : KVMemory) : Option Access → Prop
  | none => True
  | some a => AccessSafe cfg mem a

/-- A launched thread steps without faulting, keeps the invariant, and accesses safely. -/
theorem step_safe (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
    (ht : tid < cfg.numThreads) :
    ∃ next access, step cfg mem tid s = .ok (next, access) ∧
      Invariant cfg mem next ∧ EventSafe cfg mem access := by
  have hi := (hinv tid).1
  have ho := (hinv tid).2
  -- one case per instruction
  cases hp : (s.threads tid).instr with
  | guard =>
    by_cases hn : tid < cfg.numTokens
    · -- real thread: go to `.page`
      refine ⟨withThread s tid { s.threads tid with instr := .page }, none, ?_, ?_, trivial⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · apply withThread_invariant hinv
        · simpa [ThreadOK] using hn
        · simpa [hp, hn] using ho
    · -- padded thread: go to `.done`
      refine ⟨withThread s tid { s.threads tid with instr := .done }, none, ?_, ?_, trivial⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · apply withThread_invariant hinv
        · trivial
        · simpa [hp, hn] using ho
  | page =>
    have hn : tid < cfg.numTokens := by simpa [ThreadOK, hp] using hi
    refine ⟨withThread s tid { s.threads tid with
        instr := .table, logicalPage := tid / cfg.pageSize },
      none, ?_, ?_, trivial⟩
    · simp [step, Nat.not_le_of_gt ht, hp] <;> rfl
    · apply withThread_invariant hinv
      · exact ⟨hn, rfl⟩
      · simpa [hp] using ho
  | table =>
    have hi' : tid < cfg.numTokens ∧ (s.threads tid).logicalPage = tid / cfg.pageSize := by
      simpa [ThreadOK, hp] using hi
    -- the page-table read is in bounds (table_bounds)
    have hb : (s.threads tid).logicalPage < mem.pageTable.size := by
      rw [hi'.2]; exact table_bounds hvalid hi'.1
    refine ⟨withThread s tid { s.threads tid with
        instr := .kvIndex, physicalPage := physicalPage mem (s.threads tid).logicalPage },
      some ⟨tid, .pageTable, (s.threads tid).logicalPage⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hb] <;> rfl
    · apply withThread_invariant hinv
      · exact ⟨hi'.1, congrArg (physicalPage mem) hi'.2⟩
      · simpa [hp] using ho
    · exact ⟨ht, hi'.1, hb⟩
  | kvIndex =>
    have hi' : tid < cfg.numTokens ∧
        (s.threads tid).physicalPage = physicalPage mem (tid / cfg.pageSize) := by
      simpa [ThreadOK, hp] using hi
    refine ⟨withThread s tid { s.threads tid with
        instr := .load, kvIndex := (s.threads tid).physicalPage * cfg.pageSize + tid % cfg.pageSize },
      none, ?_, ?_, trivial⟩
    · simp [step, Nat.not_le_of_gt ht, hp] <;> rfl
    · apply withThread_invariant hinv
      · constructor
        · exact hi'.1
        · simp [kvIndex, hi'.2]
      · simpa [hp] using ho
  | load =>
    have hi' : tid < cfg.numTokens ∧ (s.threads tid).kvIndex = kvIndex cfg mem tid := by
      simpa [ThreadOK, hp] using hi
    -- the KV-cache read is in bounds (kvCache_bounds)
    have hb : (s.threads tid).kvIndex < mem.kvCache.size := by
      rw [hi'.2]; exact kvCache_bounds hvalid hi'.1
    refine ⟨withThread s tid { s.threads tid with
        instr := .store, entry := mem.kvCache[(s.threads tid).kvIndex]! },
      some ⟨tid, .kvCache, (s.threads tid).kvIndex⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hb] <;> rfl
    · apply withThread_invariant hinv
      · exact ⟨hi'.1, congrArg (fun i => mem.kvCache[i]!) hi'.2⟩
      · simpa [hp] using ho
    · exact ⟨ht, hi'.1, hb⟩
  | store =>
    have hi' : tid < cfg.numTokens ∧ (s.threads tid).entry = expectedEntry cfg mem tid := by
      simpa [ThreadOK, hp] using hi
    -- the output write goes to slot `tid`, in bounds because tid < numTokens
    refine ⟨withOutput (withThread s tid { s.threads tid with instr := .done }) tid
        (s.threads tid).entry,
      some ⟨tid, .output, tid⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hi'.1] <;> rfl
    · exact store_invariant hinv hi'.1 hi'.2
    · exact ⟨ht, hi'.1, rfl, hi'.1⟩
  | done =>
    exact ⟨s, none, by simp [step, Nat.not_le_of_gt ht, hp] <;> rfl, hinv, trivial⟩

/-- Any schedule of launched threads runs without faults; it need not finish. -/
theorem run_safe (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads) :
    ∃ last accesses, run cfg mem schedule s = .ok (last, accesses) ∧
      Invariant cfg mem last ∧ ∀ a ∈ accesses, AccessSafe cfg mem a := by
  induction schedule generalizing s with
  | nil => exact ⟨s, [], rfl, hinv, by simp⟩
  | cons tid schedule ih =>
    -- first step is safe (step_safe), the rest by induction
    obtain ⟨next, access, hstep, hnext, ha⟩ :=
      step_safe hvalid hinv (hschedule tid (by simp))
    obtain ⟨last, accesses, hrun, hlast, has⟩ :=
      ih hnext (fun j hj => hschedule j (by simp [hj]))
    refine ⟨last, access.toList ++ accesses, ?_, hlast, ?_⟩
    · simp only [run, hstep]
      change (do let (last, accesses) ← run cfg mem schedule next
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

def Finished (cfg : Config) (s : KernelState) : Prop :=
  ∀ tid, tid < cfg.numThreads → (s.threads tid).instr = .done

@[simp] theorem completed_eq_true : completed cfg s = true ↔ Finished cfg s := by
  simp [completed, Finished, List.all_eq_true]

-- once every thread is done, the invariant says each output slot holds the expected entry
theorem finished_correct (hvalid : ValidLaunch cfg mem)
    (hinv : Invariant cfg mem s) (hfinished : Finished cfg s)
    (ht : tid < cfg.numTokens) : s.output tid = some (expectedEntry cfg mem tid) := by
  have hd := hfinished tid (Nat.lt_of_lt_of_le ht hvalid.2.1)
  simpa [ht, hd] using (hinv tid).2

/-- For ANY schedule that finishes: output matches the spec, and every access was safe. -/
theorem completed_execution_correct (hvalid : ValidLaunch cfg mem)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads)
    (hrun : run cfg mem schedule initialState = .ok (last, accesses))
    (hdone : completed cfg last = true) :
    (∀ tid, tid < cfg.numTokens → last.output tid = some (expectedEntry cfg mem tid)) ∧
    (∀ a ∈ accesses, AccessSafe cfg mem a) := by
  obtain ⟨last', accesses', hr, hi, ha⟩ := run_safe hvalid initial_invariant hschedule
  rw [hrun] at hr
  cases hr
  exact ⟨fun _ ht => finished_correct hvalid hi (completed_eq_true.mp hdone) ht, ha⟩

/-- Padded threads make no memory accesses. -/
theorem padded_threads_no_access (h : AccessSafe cfg mem a) : a.thread < cfg.numTokens :=
  h.2.1

/-- Two different threads never write the same output slot. -/
theorem distinct_threads_disjoint_stores (ha : AccessSafe cfg mem a)
    (hb : AccessSafe cfg mem b) (hsa : a.buffer = .output) (hsb : b.buffer = .output)
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

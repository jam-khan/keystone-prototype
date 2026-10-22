import Keystone.GPU.KVGather

namespace Keystone.GPU

/-- What a thread has computed so far is correct for its next instruction. -/
def ThreadOK (cfg : Config) (mem : KVMemory) (tid : Nat) (thread : Thread) : Prop :=
  match thread.instr with
  | .guard | .done => True
  | .page    => tid < cfg.numTokens
  | .table   => tid < cfg.numTokens ∧ thread.logicalPage  = tid / cfg.pageSize
  | .kvIndex => tid < cfg.numTokens ∧ thread.physicalPage = physicalPage mem (tid / cfg.pageSize)
  | .load    => tid < cfg.numTokens ∧ thread.kvIndex      = kvIndex cfg mem tid
  | .store   => tid < cfg.numTokens ∧ thread.entry        = expectedEntry cfg mem tid

/-- An output slot is filled exactly when its real thread finishes, with the expected entry. -/
def Invariant (cfg : Config) (mem : KVMemory) (s : KernelState) : Prop :=
  ∀ tid, ThreadOK cfg mem tid (s.threads tid) ∧
    s.output tid = if tid < cfg.numTokens ∧ (s.threads tid).instr = .done
      then some (expectedEntry cfg mem tid) else none

@[simp] theorem initial_invariant : Invariant cfg mem initialState := by
  intro tid
  simp [ThreadOK, initialState]

/-- A real thread's `.table` read is inside the page table. -/
theorem table_bounds (h : ValidLaunch cfg mem) (ht : tid < cfg.numTokens) :
    tid / cfg.pageSize < mem.pageTable.size := by
  have hlt : tid < mem.pageTable.size * cfg.pageSize := Nat.lt_of_lt_of_le ht h.2.2.1
  exact (Nat.div_lt_iff_lt_mul h.1).mpr hlt

/-- A real thread's `.load` read is inside the KV cache. -/
theorem kvCache_bounds (h : ValidLaunch cfg mem) (ht : tid < cfg.numTokens) :
    kvIndex cfg mem tid < mem.kvCache.size := by
  have hp := h.2.2.2 ⟨tid / cfg.pageSize, table_bounds h ht⟩
  have hm := Nat.mod_lt tid h.1
  dsimp [kvIndex] at *
  omega

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

private theorem store_invariant (h : Invariant cfg mem s)
    (ht : tid < cfg.numTokens) (hv : entry = expectedEntry cfg mem tid) :
    Invariant cfg mem
      (withOutput (withThread s tid { s.threads tid with instr := .done }) tid entry) := by
  intro j
  by_cases hj : j = tid
  · subst j
    simp [withOutput, withThread, ThreadOK, ht, hv]
  · simpa [withOutput, withThread, hj] using h j

/-- Accesses stay in bounds; output stores use the accessing thread's own slot. -/
def AccessSafe (cfg : Config) (mem : KVMemory) (a : Access) : Prop :=
  a.thread < cfg.numThreads ∧ a.thread < cfg.numTokens ∧ match a.buffer with
    | .pageTable => a.index < mem.pageTable.size
    | .kvCache   => a.index < mem.kvCache.size
    | .output    => a.index = a.thread ∧ a.index < cfg.numTokens

def EventSafe (cfg : Config) (mem : KVMemory) : Option Access → Prop
  | none => True
  | some a => AccessSafe cfg mem a

/-- A launched thread steps without faults and preserves the invariant. -/
theorem step_safe (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
    (ht : tid < cfg.numThreads) :
    ∃ next access, step cfg mem tid s = .ok (next, access) ∧
      Invariant cfg mem next ∧ EventSafe cfg mem access := by
  have hi := (hinv tid).1
  have ho := (hinv tid).2
  cases hp : (s.threads tid).instr with
  | guard =>
    by_cases hn : tid < cfg.numTokens
    · refine ⟨withThread s tid { s.threads tid with instr := .page }, none, ?_, ?_, trivial⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · apply withThread_invariant hinv
        · simpa [ThreadOK] using hn
        · simpa [hp, hn] using ho
    · refine ⟨withThread s tid { s.threads tid with instr := .done }, none, ?_, ?_, trivial⟩
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
    refine ⟨withOutput (withThread s tid { s.threads tid with instr := .done }) tid
        (s.threads tid).entry,
      some ⟨tid, .output, tid⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hi'.1] <;> rfl
    · exact store_invariant hinv hi'.1 hi'.2
    · exact ⟨ht, hi'.1, rfl, hi'.1⟩
  | done =>
    exact ⟨s, none, by simp [step, Nat.not_le_of_gt ht, hp] <;> rfl, hinv, trivial⟩

/-- Any finite schedule of launched threads is safe; completion is separate. -/
theorem run_safe (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads) :
    ∃ last accesses, run cfg mem schedule s = .ok (last, accesses) ∧
      Invariant cfg mem last ∧ ∀ a ∈ accesses, AccessSafe cfg mem a := by
  induction schedule generalizing s with
  | nil => exact ⟨s, [], rfl, hinv, by simp⟩
  | cons tid schedule ih =>
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

def Finished (cfg : Config) (s : KernelState) : Prop :=
  ∀ tid, tid < cfg.numThreads → (s.threads tid).instr = .done

@[simp] theorem completed_eq_true : completed cfg s = true ↔ Finished cfg s := by
  simp [completed, Finished, List.all_eq_true]

theorem finished_correct (hvalid : ValidLaunch cfg mem)
    (hinv : Invariant cfg mem s) (hfinished : Finished cfg s)
    (ht : tid < cfg.numTokens) : s.output tid = some (expectedEntry cfg mem tid) := by
  have hd := hfinished tid (Nat.lt_of_lt_of_le ht hvalid.2.1)
  simpa [ht, hd] using (hinv tid).2

/-- Completed executions match the specification, for any schedule. -/
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

/-- Padded threads produce no memory accesses. -/
theorem padded_threads_no_access (h : AccessSafe cfg mem a) : a.thread < cfg.numTokens :=
  h.2.1

/-- Stores from distinct threads cannot conflict. -/
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

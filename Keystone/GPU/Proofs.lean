import Keystone.GPU.Model

namespace Keystone.GPU

/-- Register invariants at each instruction boundary. -/
def LaneOK (cfg : Config) (input : Input) (tid : Nat) (l : Lane) : Prop :=
  match l.pc with
  | .guard | .done => True
  | .index => tid < cfg.n
  | .table => tid < cfg.n ∧ l.page = tid / cfg.pageSize
  | .address => tid < cfg.n ∧ l.physical = physicalPage input (tid / cfg.pageSize)
  | .load => tid < cfg.n ∧ l.address = gatherAddress cfg input tid
  | .store => tid < cfg.n ∧ l.value = referenceAt cfg input tid

/-- An output slot is populated exactly when its active owner lane finishes. -/
def Invariant (cfg : Config) (input : Input) (m : Machine) : Prop :=
  ∀ tid, LaneOK cfg input tid (m.threads tid) ∧
    m.output tid = if tid < cfg.n ∧ (m.threads tid).pc = .done
      then some (referenceAt cfg input tid) else none

@[simp] theorem initial_invariant : Invariant cfg input init := by
  intro tid
  simp [LaneOK, init]

theorem table_bounds (h : ValidInput cfg input) (ht : tid < cfg.n) :
    tid / cfg.pageSize < input.pageTable.size := by
  have hlt : tid < input.pageTable.size * cfg.pageSize := Nat.lt_of_lt_of_le ht h.2.2.1
  exact (Nat.div_lt_iff_lt_mul h.1).mpr hlt

theorem cache_bounds (h : ValidInput cfg input) (ht : tid < cfg.n) :
    gatherAddress cfg input tid < input.cache.size := by
  have hp := h.2.2.2 ⟨tid / cfg.pageSize, table_bounds h ht⟩
  have hm := Nat.mod_lt tid h.1
  dsimp [gatherAddress] at *
  omega

private theorem withLane_invariant (h : Invariant cfg input m)
    (hl : LaneOK cfg input tid l)
    (ho : m.output tid = if tid < cfg.n ∧ l.pc = .done
      then some (referenceAt cfg input tid) else none) :
    Invariant cfg input (withLane m tid l) := by
  intro j
  by_cases hj : j = tid
  · subst j
    simpa [withLane] using And.intro hl ho
  · simpa [withLane, hj] using h j

private theorem store_invariant (h : Invariant cfg input m)
    (ht : tid < cfg.n) (hv : value = referenceAt cfg input tid) :
    Invariant cfg input
      (withOutput (withLane m tid { m.threads tid with pc := .done }) tid value) := by
  intro j
  by_cases hj : j = tid
  · subst j
    simp [withOutput, withLane, LaneOK, ht, hv]
  · simpa [withOutput, withLane, hj] using h j

/-- Events stay within bounds; output stores use the emitting lane’s own slot. -/
def AccessSafe (cfg : Config) (input : Input) (a : Access) : Prop :=
  a.lane < cfg.lanes ∧ a.lane < cfg.n ∧ match a.space with
    | .pageTable => a.address < input.pageTable.size
    | .cache => a.address < input.cache.size
    | .output => a.address = a.lane ∧ a.address < cfg.n

def EventSafe (cfg : Config) (input : Input) : Option Access → Prop
  | none => True
  | some a => AccessSafe cfg input a

/-- A launched lane steps without faults and preserves the invariant. -/
theorem step_safe (hvalid : ValidInput cfg input) (hinv : Invariant cfg input m)
    (ht : tid < cfg.lanes) :
    ∃ next access, step cfg input tid m = .ok (next, access) ∧
      Invariant cfg input next ∧ EventSafe cfg input access := by
  have hi := (hinv tid).1
  have ho := (hinv tid).2
  cases hp : (m.threads tid).pc with
  | guard =>
    by_cases hn : tid < cfg.n
    · refine ⟨withLane m tid { m.threads tid with pc := .index }, none, ?_, ?_, trivial⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · apply withLane_invariant hinv
        · simpa [LaneOK] using hn
        · simpa [hp, hn] using ho
    · refine ⟨withLane m tid { m.threads tid with pc := .done }, none, ?_, ?_, trivial⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · apply withLane_invariant hinv
        · trivial
        · simpa [hp, hn] using ho
  | index =>
    have hn : tid < cfg.n := by simpa [LaneOK, hp] using hi
    refine ⟨withLane m tid { m.threads tid with pc := .table, page := tid / cfg.pageSize }, none, ?_, ?_, trivial⟩
    · simp [step, Nat.not_le_of_gt ht, hp] <;> rfl
    · apply withLane_invariant hinv
      · exact ⟨hn, rfl⟩
      · simpa [hp] using ho
  | table =>
    have hi' : tid < cfg.n ∧ (m.threads tid).page = tid / cfg.pageSize := by
      simpa [LaneOK, hp] using hi
    have hb : (m.threads tid).page < input.pageTable.size := by
      rw [hi'.2]; exact table_bounds hvalid hi'.1
    refine ⟨withLane m tid { m.threads tid with pc := .address, physical := physicalPage input (m.threads tid).page },
      some ⟨tid, .pageTable, (m.threads tid).page⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, hb] <;> rfl
    · apply withLane_invariant hinv
      · exact ⟨hi'.1, congrArg (physicalPage input) hi'.2⟩
      · simpa [hp] using ho
    · exact ⟨ht, hi'.1, hb⟩
  | address =>
    have hi' : tid < cfg.n ∧ (m.threads tid).physical = physicalPage input (tid / cfg.pageSize) := by
      simpa [LaneOK, hp] using hi
    refine ⟨withLane m tid { m.threads tid with pc := .load, address := (m.threads tid).physical * cfg.pageSize + tid % cfg.pageSize }, none, ?_, ?_, trivial⟩
    · simp [step, Nat.not_le_of_gt ht, hp] <;> rfl
    · apply withLane_invariant hinv
      · constructor
        · exact hi'.1
        · simp [gatherAddress, hi'.2]
      · simpa [hp] using ho
  | load =>
    have hi' : tid < cfg.n ∧ (m.threads tid).address = gatherAddress cfg input tid := by
      simpa [LaneOK, hp] using hi
    have hb : (m.threads tid).address < input.cache.size := by
      rw [hi'.2]; exact cache_bounds hvalid hi'.1
    refine ⟨withLane m tid { m.threads tid with pc := .store, value := input.cache[(m.threads tid).address]! },
      some ⟨tid, .cache, (m.threads tid).address⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, hb] <;> rfl
    · apply withLane_invariant hinv
      · exact ⟨hi'.1, congrArg (fun a => input.cache[a]!) hi'.2⟩
      · simpa [hp] using ho
    · exact ⟨ht, hi'.1, hb⟩
  | store =>
    have hi' : tid < cfg.n ∧ (m.threads tid).value = referenceAt cfg input tid := by
      simpa [LaneOK, hp] using hi
    refine ⟨withOutput (withLane m tid { m.threads tid with pc := .done }) tid (m.threads tid).value,
      some ⟨tid, .output, tid⟩, ?_, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, hi'.1] <;> rfl
    · exact store_invariant hinv hi'.1 hi'.2
    · exact ⟨ht, hi'.1, rfl, hi'.1⟩
  | done =>
    exact ⟨m, none, by simp [step, Nat.not_le_of_gt ht, hp] <;> rfl, hinv, trivial⟩

/-- Any finite schedule of launched lanes is safe; completion is separate. -/
theorem run_safe (hvalid : ValidInput cfg input) (hinv : Invariant cfg input m)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.lanes) :
    ∃ last accesses, run cfg input schedule m = .ok (last, accesses) ∧
      Invariant cfg input last ∧ ∀ a ∈ accesses, AccessSafe cfg input a := by
  induction schedule generalizing m with
  | nil => exact ⟨m, [], rfl, hinv, by simp⟩
  | cons tid schedule ih =>
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

def Finished (cfg : Config) (m : Machine) : Prop :=
  ∀ tid, tid < cfg.lanes → (m.threads tid).pc = .done

@[simp] theorem completed_eq_true : completed cfg m = true ↔ Finished cfg m := by
  simp [completed, Finished, List.all_eq_true]

theorem finished_correct (hvalid : ValidInput cfg input)
    (hinv : Invariant cfg input m) (hfinished : Finished cfg m)
    (ht : tid < cfg.n) : m.output tid = some (referenceAt cfg input tid) := by
  have hd := hfinished tid (Nat.lt_of_lt_of_le ht hvalid.2.1)
  simpa [ht, hd] using (hinv tid).2

/-- Completed executions match the sequential gather. -/
theorem completed_execution_correct (hvalid : ValidInput cfg input)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.lanes)
    (hrun : run cfg input schedule init = .ok (last, accesses))
    (hdone : completed cfg last = true) :
    (∀ tid, tid < cfg.n → last.output tid = some (referenceAt cfg input tid)) ∧
    (∀ a ∈ accesses, AccessSafe cfg input a) := by
  obtain ⟨last', accesses', hr, hi, ha⟩ := run_safe hvalid initial_invariant hschedule
  rw [hrun] at hr
  cases hr
  exact ⟨fun _ ht => finished_correct hvalid hi (completed_eq_true.mp hdone) ht, ha⟩

/-- Padded lanes produce no memory events. -/
theorem padded_lanes_no_access (h : AccessSafe cfg input a) : a.lane < cfg.n := h.2.1

/-- Stores from distinct lanes cannot conflict. -/
theorem distinct_lanes_disjoint_stores (ha : AccessSafe cfg input a)
    (hb : AccessSafe cfg input b) (hsa : a.space = .output) (hsb : b.space = .output)
    (hne : a.lane ≠ b.lane) : a.address ≠ b.address := by
  have hae : a.address = a.lane := by
    have h := ha.2.2
    rw [hsa] at h
    exact h.1
  have hbe : b.address = b.lane := by
    have h := hb.2.2
    rw [hsb] at h
    exact h.1
  simpa [hae, hbe] using hne

end Keystone.GPU

import Keystone.GPU.KVGather -- Kernel state, execution, and launch conditions.

/-!
# Auxiliary: proof infrastructure for `Properties.lean`

1. Bounds and grid-stride arithmetic.
2. The invariant every reachable state satisfies (`ThreadOK`, `Filled`, `Invariant`),
   and `step_safe`: a launched thread steps without faulting and keeps the invariant.
3. Stores: each store fills a slot that was empty.
4. Progress: each thread's countdown `remaining`.
-/

namespace Keystone.GPU

/-! ## Bounds: a valid launch keeps both reads in bounds -/

/-- Token `t`'s `.table` read is inside the page table. -/
theorem table_bounds
  (h : ValidLaunch cfg mem)
  (ht : t < cfg.numTokens)
    : t / cfg.pageSize < mem.pageTable.size := by
  unfold ValidLaunch at h
  -- h : 0 < pageSize ∧ 0 < numThreads ∧ numTokens ≤ pageTable.size * pageSize ∧ ∀ p, …
  -- name the four conjuncts in order (`_` prefix = unused here)
  obtain ⟨hpos, _hthreads, hcapacity, _hpages⟩ := h
  -- numTokens ≤ pageTable.size * pageSize, so t < pageTable.size * pageSize
  have h1 : t < mem.pageTable.size * cfg.pageSize := Nat.lt_of_lt_of_le ht hcapacity
  -- divide both sides by pageSize (> 0)
  exact (Nat.div_lt_iff_lt_mul hpos).mpr h1

/-- Token `t`'s `.load` read is inside the KV cache. -/
theorem kvCache_bounds
  (h : ValidLaunch cfg mem)
  (ht : t < cfg.numTokens)
    : kvIndex cfg mem t < mem.kvCache.size := by
  unfold kvIndex
  -- unfold physicalPage
  -- unfold ValidLaunch at h
  have h' := table_bounds h ht
  obtain ⟨hpos, _hthreads, hcapacity, hpages⟩ := h
  have hfits := hpages ⟨t / cfg.pageSize, h'⟩
  have hoffset : t % cfg.pageSize < cfg.pageSize := by
    exact Nat.mod_lt t hpos
  simp at hfits
  have hstep := Nat.add_lt_add_left hoffset (physicalPage mem (t / cfg.pageSize) * cfg.pageSize)
  exact Nat.lt_of_lt_of_le hstep hfits

/-! ## Grid-stride arithmetic: thread `tid`'s token in round `r` is `tid + r * numThreads` -/

/-- A launched thread's tokens all have remainder `tid` mod `numThreads`... -/
theorem token_mod (ht : tid < cfg.numThreads) : token cfg tid r % cfg.numThreads = tid := by
  unfold token
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

/-- ... and quotient `r`, the round. So each token has exactly one owner and round. -/
theorem token_div (ht : tid < cfg.numThreads) : token cfg tid r / cfg.numThreads = r := by
  unfold token
  rw [Nat.add_mul_div_right _ _ (Nat.lt_of_le_of_lt (Nat.zero_le tid) ht),
    Nat.div_eq_of_lt ht, Nat.zero_add]

/-- A thread with a token left is in a round below `numRounds = ⌈numTokens / numThreads⌉`. -/
private theorem round_lt_numRounds (ht : tid < cfg.numThreads)
    (h : token cfg tid r < cfg.numTokens) : r < numRounds cfg := by
  unfold numRounds
  unfold token at h
  apply Nat.not_le.mp
  intro hle
  -- r ≥ ⌈N / T⌉ would give r * T ≥ N, but tid + r * T < N
  have hmul := Nat.mul_le_mul_right cfg.numThreads hle
  have hd := Nat.div_add_mod (cfg.numTokens + cfg.numThreads - 1) cfg.numThreads
  have hm := Nat.mod_lt (cfg.numTokens + cfg.numThreads - 1)
    (Nat.lt_of_le_of_lt (Nat.zero_le tid) ht)
  rw [Nat.mul_comm] at hd
  omega

/-! ## The invariant: what every reachable state satisfies -/

/--
  `ThreadOK` is a predicate to ensure an invariant for a thread during
  steps. So, essentially, it states the properties a thread would hold
  under which `instr` instruction set.
  `t` is the thread's current token, `tid + round * numThreads`.
-/
def ThreadOK (cfg : Config) (mem : KVMemory) (tid : Nat) (thread : Thread) : Prop :=
  let B := cfg.pageSize
  let t := token cfg tid thread.round
  match thread.instr with
  | .guard   => True
  | .done    => cfg.numTokens ≤ t      -- no tokens left
  | .page    => t < cfg.numTokens
  | .table   =>
      t < cfg.numTokens
    ∧ thread.logicalPage  = t / B
  | .kvIndex =>
      t < cfg.numTokens
    ∧ thread.physicalPage = mem.pageTable[t / B]!
  | .load    =>
      t < cfg.numTokens
    ∧ thread.kvIndex = mem.pageTable[t / B]! * B + t % B
  | .store   =>
      t < cfg.numTokens
    ∧ thread.entry = mem.kvCache[mem.pageTable[t / B]! * B + t % B]!

/--
  Output slot `e` has been written: its owner thread `e % numThreads`
  has finished the round `e / numThreads` that handles it.
-/
def Filled (cfg : Config) (s : KernelState) (e : Nat) : Prop :=
  e / cfg.numThreads < (s.threads (e % cfg.numThreads)).round

instance : Decidable (Filled cfg s e) := inferInstanceAs (Decidable (_ < _))

/--
  Every thread is OK, and output slot `e` holds the expected entry
  exactly when it has been written.
-/
def Invariant (cfg : Config) (mem : KVMemory) (s : KernelState) : Prop :=
  (∀ tid, ThreadOK cfg mem tid (s.threads tid)) ∧
  (∀ e, s.output e = if Filled cfg s e then some (expectedEntry cfg mem e) else none)

-- the initial state satisfies the invariant: every thread at `.guard` in round 0, no outputs
@[simp] theorem initial_invariant : Invariant cfg mem initialState := by
  constructor
  · intro tid
    simp [ThreadOK, initialState]
  · intro e
    simp [initialState, Filled]

-- replacing one thread's state keeps the invariant, if the new state is OK
-- and its round is unchanged
private theorem withThread_invariant (h : Invariant cfg mem s)
    (hthread : ThreadOK cfg mem tid thread)
    (hround : thread.round = (s.threads tid).round) :
    Invariant cfg mem (withThread s tid thread) := by
  refine ⟨fun j => ?_, fun e => ?_⟩
  · by_cases hj : j = tid
    · subst j
      simpa [withThread] using hthread
    · simpa [withThread, hj] using h.1 j
  · have hfill : Filled cfg (withThread s tid thread) e ↔ Filled cfg s e := by
      unfold Filled
      by_cases he : e % cfg.numThreads = tid
      · simp [withThread, he, hround]
      · simp [withThread, he]
    change s.output e = _
    rw [h.2 e]
    simp only [hfill]

-- `.store` keeps the invariant: it fills slot `t` with the expected entry
-- and moves the thread to its next round
private theorem store_invariant (h : Invariant cfg mem s) (ht : tid < cfg.numThreads)
    (hv : (s.threads tid).entry = expectedEntry cfg mem (token cfg tid (s.threads tid).round)) :
    Invariant cfg mem
      (withOutput (withThread s tid { s.threads tid with
          instr := .guard, round := (s.threads tid).round + 1 })
        (token cfg tid (s.threads tid).round) (s.threads tid).entry) := by
  refine ⟨fun j => ?_, fun e => ?_⟩
  · by_cases hj : j = tid
    · subst j
      simp [withOutput, withThread, ThreadOK]
    · simpa [withOutput, withThread, hj] using h.1 j
  · by_cases het : e = token cfg tid (s.threads tid).round
    · -- the slot just written: its owner is now one round further
      subst het
      simp [Filled, withOutput, withThread, token_mod ht, token_div ht, hv]
    · -- any other slot: same contents, same filled-ness
      have hfill : Filled cfg (withOutput (withThread s tid { s.threads tid with
          instr := .guard, round := (s.threads tid).round + 1 })
          (token cfg tid (s.threads tid).round) (s.threads tid).entry) e ↔ Filled cfg s e := by
        unfold Filled
        by_cases he : e % cfg.numThreads = tid
        · -- same owner: e is not in this round, because then e would be `t`
          have hq : e / cfg.numThreads ≠ (s.threads tid).round := by
            intro hq
            apply het
            have hd := Nat.mod_add_div e cfg.numThreads
            rw [he, hq] at hd
            simp only [token]
            rw [Nat.mul_comm]
            omega
          simp [withOutput, withThread, he]
          omega
        · simp [withOutput, withThread, he]
      change (if e = token cfg tid (s.threads tid).round then some (s.threads tid).entry
        else s.output e) = _
      rw [ite_eq_right het, h.2 e]
      simp only [hfill]

/-- A launched thread steps without faulting and keeps the invariant. -/
theorem step_safe (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
    (ht : tid < cfg.numThreads) :
    ∃ next access, step cfg mem tid s = .ok (next, access) ∧ Invariant cfg mem next := by
  have hi := hinv.1 tid
  -- one case per instruction
  cases hp : (s.threads tid).instr with
  | guard =>
    by_cases hn : token cfg tid (s.threads tid).round < cfg.numTokens
    · -- a token is left: go to `.page`
      refine ⟨withThread s tid { s.threads tid with instr := .page }, none, ?_, ?_⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · exact withThread_invariant hinv (by simpa [ThreadOK] using hn) rfl
    · -- no tokens left: go to `.done`
      refine ⟨withThread s tid { s.threads tid with instr := .done }, none, ?_, ?_⟩
      · simp [step, Nat.not_le_of_gt ht, hp, hn] <;> rfl
      · exact withThread_invariant hinv (by simpa [ThreadOK] using hn) rfl
  | page =>
    have hn : token cfg tid (s.threads tid).round < cfg.numTokens := by
      simpa [ThreadOK, hp] using hi
    refine ⟨withThread s tid { s.threads tid with
        instr := .table, logicalPage := token cfg tid (s.threads tid).round / cfg.pageSize },
      none, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp] <;> rfl
    · exact withThread_invariant hinv ⟨hn, rfl⟩ rfl
  | table =>
    have hi' : token cfg tid (s.threads tid).round < cfg.numTokens ∧
        (s.threads tid).logicalPage = token cfg tid (s.threads tid).round / cfg.pageSize := by
      simpa [ThreadOK, hp] using hi
    -- the page-table read is in bounds (table_bounds)
    have hb : (s.threads tid).logicalPage < mem.pageTable.size := by
      rw [hi'.2]; exact table_bounds hvalid hi'.1
    refine ⟨withThread s tid { s.threads tid with
        instr := .kvIndex, physicalPage := physicalPage mem (s.threads tid).logicalPage },
      some ⟨tid, .pageTable, (s.threads tid).logicalPage⟩, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hb] <;> rfl
    · exact withThread_invariant hinv ⟨hi'.1, congrArg (physicalPage mem) hi'.2⟩ rfl
  | kvIndex =>
    have hi' : token cfg tid (s.threads tid).round < cfg.numTokens ∧
        (s.threads tid).physicalPage =
          mem.pageTable[token cfg tid (s.threads tid).round / cfg.pageSize]! := by
      simpa [ThreadOK, hp] using hi
    refine ⟨withThread s tid { s.threads tid with
        instr := .load, kvIndex := (s.threads tid).physicalPage * cfg.pageSize +
          token cfg tid (s.threads tid).round % cfg.pageSize },
      none, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp] <;> rfl
    · refine withThread_invariant hinv ⟨hi'.1, ?_⟩ rfl
      simp [hi'.2]
  | load =>
    have hi' : token cfg tid (s.threads tid).round < cfg.numTokens ∧ (s.threads tid).kvIndex =
        mem.pageTable[token cfg tid (s.threads tid).round / cfg.pageSize]! * cfg.pageSize +
          token cfg tid (s.threads tid).round % cfg.pageSize := by
      simpa [ThreadOK, hp] using hi
    -- the KV-cache read is in bounds (kvCache_bounds)
    have hb : (s.threads tid).kvIndex < mem.kvCache.size := by
      rw [hi'.2]; exact kvCache_bounds hvalid hi'.1
    refine ⟨withThread s tid { s.threads tid with
        instr := .store, entry := mem.kvCache[(s.threads tid).kvIndex]! },
      some ⟨tid, .kvCache, (s.threads tid).kvIndex⟩, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hb] <;> rfl
    · exact withThread_invariant hinv ⟨hi'.1, congrArg (fun i => mem.kvCache[i]!) hi'.2⟩ rfl
  | store =>
    have hi' : token cfg tid (s.threads tid).round < cfg.numTokens ∧ (s.threads tid).entry =
        mem.kvCache[mem.pageTable[token cfg tid (s.threads tid).round / cfg.pageSize]! *
          cfg.pageSize + token cfg tid (s.threads tid).round % cfg.pageSize]! := by
      simpa [ThreadOK, hp] using hi
    -- the output write goes to slot `t`, which is inside the output (t < numTokens)
    refine ⟨withOutput (withThread s tid { s.threads tid with
          instr := .guard, round := (s.threads tid).round + 1 })
        (token cfg tid (s.threads tid).round) (s.threads tid).entry,
      some ⟨tid, .output, token cfg tid (s.threads tid).round⟩, ?_, ?_⟩
    · simp [step, Nat.not_le_of_gt ht, hp, Nat.not_le_of_gt hi'.1] <;> rfl
    · exact store_invariant hinv ht hi'.2
  | done =>
    exact ⟨s, none, by simp [step, Nat.not_le_of_gt ht, hp] <;> rfl, hinv⟩

-- once every thread is done, every output slot holds the expected entry
theorem finished_correct (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
    (hfinished : ∀ tid, tid < cfg.numThreads → (s.threads tid).instr = .done)
    (he : e < cfg.numTokens) : s.output e = some (expectedEntry cfg mem e) := by
  -- slot e belongs to thread `e % numThreads`, which handles it in round `e / numThreads`
  have hT : 0 < cfg.numThreads := hvalid.2.1
  have hdone := hinv.1 (e % cfg.numThreads)
  simp only [ThreadOK, hfinished _ (Nat.mod_lt e hT)] at hdone
  -- that thread is done, so its token passed numTokens > e: it is past e's round
  have hfill : Filled cfg s e := by
    unfold Filled
    apply Nat.not_le.mp
    intro hle
    have hmul := Nat.mul_le_mul_right cfg.numThreads hle
    have hd := Nat.mod_add_div e cfg.numThreads
    rw [Nat.mul_comm] at hd
    simp only [token] at hdone
    omega
  rw [hinv.2 e, ite_eq_left hfill]

/-! ## Stores: each store fills a slot that was empty -/

-- a step never lowers any thread's round
private theorem step_round_mono (ht : tid < cfg.numThreads)
    (hs : step cfg mem tid s = .ok (next, access)) (j : Nat) :
    (s.threads j).round ≤ (next.threads j).round := by
  cases hp : (s.threads tid).instr <;>
    simp [step, Nat.not_le_of_gt ht, hp] at hs
  all_goals try split at hs
  all_goals try cases hs
  all_goals by_cases hj : j = tid <;> simp_all [withThread, withOutput]

-- a store writes the thread's current token, and moves the thread to the next round
private theorem step_store (ht : tid < cfg.numThreads)
    (hs : step cfg mem tid s = .ok (next, some a)) (hout : a.buffer = .output) :
    a.index = token cfg tid (s.threads tid).round ∧
      (next.threads tid).round = (s.threads tid).round + 1 := by
  cases hp : (s.threads tid).instr <;>
    simp [step, Nat.not_le_of_gt ht, hp] at hs
  all_goals try split at hs
  all_goals try cases hs
  all_goals simp_all [withThread, withOutput]

-- so a store hits a slot that was empty before the step and is filled after it
private theorem step_store_fresh (ht : tid < cfg.numThreads)
    (hs : step cfg mem tid s = .ok (next, some a)) (hout : a.buffer = .output) :
    ¬ Filled cfg s a.index ∧ Filled cfg next a.index := by
  obtain ⟨hidx, hround⟩ := step_store ht hs hout
  unfold Filled
  rw [hidx, token_mod ht, token_div ht, hround]
  omega

-- and filled slots stay filled
private theorem step_filled_mono (ht : tid < cfg.numThreads)
    (hs : step cfg mem tid s = .ok (next, access)) (h : Filled cfg s e) : Filled cfg next e :=
  Nat.lt_of_lt_of_le h (step_round_mono ht hs _)

-- every store in a run hits a slot that was empty at the start, and no two hit the same slot
theorem run_stores_fresh (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads)
    (hrun : run cfg mem schedule s = .ok (last, accesses)) :
    (∀ a ∈ accesses, a.buffer = .output → ¬ Filled cfg s a.index) ∧
    accesses.Pairwise (fun a b => a.buffer = .output → b.buffer = .output → a.index ≠ b.index) := by
  induction schedule generalizing s accesses with
  | nil =>
    cases hrun
    simp
  | cons tid schedule ih =>
    have ht : tid < cfg.numThreads := hschedule tid (by simp)
    cases hs : step cfg mem tid s with
    | error e =>
      simp [run, hs] at hrun <;> cases hrun
    | ok pair =>
      obtain ⟨next, access⟩ := pair
      simp only [run, hs] at hrun
      change (do let v ← run cfg mem schedule next
                 pure (v.1, access.toList ++ v.2)) = Except.ok (last, accesses) at hrun
      cases hr : run cfg mem schedule next with
      | error e =>
        simp [hr] at hrun <;> cases hrun
      | ok pair =>
        obtain ⟨last', rest⟩ := pair
        simp only [hr] at hrun
        cases hrun
        obtain ⟨hfresh, hpair⟩ := ih (fun j hj => hschedule j (by simp [hj])) hr
        refine ⟨fun a ha hout => ?_, List.pairwise_append.mpr ⟨?_, hpair, ?_⟩⟩
        · rcases List.mem_append.mp ha with hleft | hright
          · -- this step's own store: the slot was empty before it
            cases access with
            | none => simp at hleft
            | some b =>
              have hab : a = b := by simpa using hleft
              subst a
              exact (step_store_fresh ht hs hout).1
          · -- a later store: empty after this step, so empty before it too
            exact fun hfilled => hfresh a hright hout (step_filled_mono ht hs hfilled)
        · cases access <;> simp
        · -- this step's store fills its slot; every later store hits an empty slot
          intro a ha b hb hao hbo heq
          cases access with
          | none => simp at ha
          | some c =>
            have hac : a = c := by simpa using ha
            subst a
            exact hfresh b hb hbo (heq ▸ (step_store_fresh ht hs hao).2)

/-! ## Progress: each thread's countdown

`remaining` drops by 1 on each of the thread's steps and is 0 only at `.done`. -/

/--
  Turns a thread still needs: 6 for this and each later round (counted down
  inside the current round), plus 1 for the final `.guard`.
-/
def remaining (cfg : Config) (thread : Thread) : Nat :=
  let left := 6 * (numRounds cfg - thread.round)
  match thread.instr with
  | .guard   => left + 1
  | .page    => left
  | .table   => left - 1
  | .kvIndex => left - 2
  | .load    => left - 3
  | .store   => left - 4
  | .done    => 0

-- a real (non-guard, non-done) instruction always has a token left
private theorem active_token_lt (hok : ThreadOK cfg mem tid thread)
    (hg : thread.instr ≠ .guard) (hd : thread.instr ≠ .done) :
    token cfg tid thread.round < cfg.numTokens := by
  unfold ThreadOK at hok
  cases hp : thread.instr <;> simp_all

/-- With the invariant, a launched thread's countdown is 0 only at `.done`. -/
theorem remaining_eq_zero (hinv : Invariant cfg mem s) (ht : tid < cfg.numThreads)
    (h0 : remaining cfg (s.threads tid) = 0) : (s.threads tid).instr = .done := by
  by_cases hg : (s.threads tid).instr = .guard
  · simp [remaining, hg] at h0
  by_cases hd : (s.threads tid).instr = .done
  · exact hd
  -- otherwise a round is left, so the countdown is at least 2
  have hr := round_lt_numRounds ht (active_token_lt (hinv.1 tid) hg hd)
  cases hp : (s.threads tid).instr <;> simp_all [remaining] <;> omega

-- each step of thread `tid` lowers its countdown by at least 1; other threads are unchanged
private theorem step_remaining (hinv : Invariant cfg mem s) (ht : tid < cfg.numThreads)
    (hs : step cfg mem tid s = .ok (next, access)) (j : Nat) :
    remaining cfg (next.threads j) ≤
      remaining cfg (s.threads j) - if j = tid then 1 else 0 := by
  -- at `.store` a round is still left, so moving to the next round costs exactly 1
  have hr : (s.threads tid).instr = .store → (s.threads tid).round < numRounds cfg := by
    intro hstore
    have hok := hinv.1 tid
    simp only [ThreadOK, hstore] at hok
    exact round_lt_numRounds ht hok.1
  cases hp : (s.threads tid).instr <;>
    simp [step, Nat.not_le_of_gt ht, hp] at hs
  all_goals try split at hs
  all_goals try cases hs
  all_goals by_cases hj : j = tid <;> simp_all [withThread, withOutput, remaining] <;> omega

/-- Each scheduled turn lowers that thread's countdown; done threads stay at 0. -/
theorem run_remaining (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
    (hschedule : ∀ t ∈ schedule, t < cfg.numThreads)
    (hrun : run cfg mem schedule s = .ok (last, accesses)) (j : Nat) :
    remaining cfg (last.threads j) ≤ remaining cfg (s.threads j) - schedule.count j := by
  induction schedule generalizing s accesses with
  | nil =>
    cases hrun
    simp
  | cons tid schedule ih =>
    have ht : tid < cfg.numThreads := hschedule tid (by simp)
    cases hs : step cfg mem tid s with
    | error e =>
      simp [run, hs] at hrun <;> cases hrun
    | ok pair =>
      obtain ⟨next, access⟩ := pair
      simp only [run, hs] at hrun
      change (do let v ← run cfg mem schedule next
                 pure (v.1, access.toList ++ v.2)) = Except.ok (last, accesses) at hrun
      cases hr : run cfg mem schedule next with
      | error e =>
        simp [hr] at hrun <;> cases hrun
      | ok pair =>
        obtain ⟨last', accesses'⟩ := pair
        simp only [hr] at hrun
        cases hrun
        -- the step keeps the invariant (step_safe), so the induction hypothesis applies
        have hnext : Invariant cfg mem next := by
          obtain ⟨next', access', hs', hinv'⟩ := step_safe hvalid hinv ht
          rw [hs] at hs'
          cases hs'
          exact hinv'
        have hind := ih hnext (fun t ht => hschedule t (by simp [ht])) hr
        have hstep := step_remaining hinv ht hs j
        by_cases hj : j = tid
        · subst j
          simp at *
          omega
        · have hj' : tid ≠ j := Ne.symm hj
          simp [hj, hj'] at *
          omega

-- `roundRobin` schedules only launched threads ...
theorem roundRobin_valid : ∀ t ∈ roundRobin cfg, t < cfg.numThreads := by
  simp [roundRobin]

private theorem count_rounds {cfg : Config} (ht : tid < cfg.numThreads) (n : Nat) :
    ((List.replicate n (List.range cfg.numThreads)).flatten).count tid = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.count_range, ht, ih] <;> omega

-- ... and gives each one `6 * numRounds + 1` turns
theorem roundRobin_count (ht : tid < cfg.numThreads) :
    (roundRobin cfg).count tid = 6 * numRounds cfg + 1 :=
  count_rounds ht _

end Keystone.GPU

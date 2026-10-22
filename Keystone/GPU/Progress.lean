import Keystone.GPU.Proofs

/-!
# Progress: every thread finishes

Safety (`Proofs.lean`) only says a run never faults; a thread that is never
scheduled stays unfinished forever. Here: each thread has a countdown,
`remaining`, that drops by 1 on each of its steps and is 0 only at `.done`.

The two main theorems:
1. `sufficiently_scheduled_finishes`: `6 * numRounds + 1` turns per thread finish every thread.
2. `verified_roundRobin`: `roundRobin` gives exactly that many turns, so it runs safely,
   finishes, and outputs `expectedOutput`.
-/

namespace Keystone.GPU

/-- A thread with a token left is in a round below `numRounds = ⌈numTokens / numThreads⌉`. -/
private theorem round_lt_numRounds (ht : tid < cfg.numThreads) (h : token cfg tid r < cfg.numTokens) :
    r < numRounds cfg := by
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
private theorem remaining_eq_zero (hinv : Invariant cfg mem s) (ht : tid < cfg.numThreads)
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
private theorem run_remaining (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
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
          obtain ⟨next', access', hs', hinv', _⟩ := step_safe hvalid hinv ht
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

/-- From the start, `6 * numRounds + 1` turns per launched thread finish every thread. -/
theorem sufficiently_scheduled_finishes (hvalid : ValidLaunch cfg mem)
    (hschedule : ∀ t ∈ schedule, t < cfg.numThreads)
    (hrun : run cfg mem schedule initialState = .ok (last, accesses))
    (hcount : ∀ t, t < cfg.numThreads → 6 * numRounds cfg + 1 ≤ schedule.count t) :
    Finished cfg last := by
  obtain ⟨last', accesses', hr', hlast, _⟩ := run_safe hvalid initial_invariant hschedule
  rw [hrun] at hr'
  cases hr'
  intro t ht
  have hrem := run_remaining hvalid initial_invariant hschedule hrun t
  have hc := hcount t ht
  have hstart : remaining cfg (initialState.threads t) = 6 * numRounds cfg + 1 := by
    simp [remaining, initialState]
  exact remaining_eq_zero hlast ht (by omega)

private theorem roundRobin_valid : ∀ t ∈ roundRobin cfg, t < cfg.numThreads := by
  simp [roundRobin]

private theorem count_rounds {cfg : Config} (ht : tid < cfg.numThreads) (n : Nat) :
    ((List.replicate n (List.range cfg.numThreads)).flatten).count tid = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.count_range, ht, ih] <;> omega

private theorem roundRobin_count (ht : tid < cfg.numThreads) :
    (roundRobin cfg).count tid = 6 * numRounds cfg + 1 :=
  count_rounds ht _

/-- A valid launch under `roundRobin` runs safely, finishes, and outputs the expected entries. -/
theorem verified_roundRobin (hvalid : ValidLaunch cfg mem) :
    ∃ last accesses,
      run cfg mem (roundRobin cfg) initialState = .ok (last, accesses) ∧
      completed cfg last = true ∧
      (∀ t, t < cfg.numTokens → last.output t = some (expectedEntry cfg mem t)) ∧
      (∀ a ∈ accesses, AccessSafe cfg mem a) := by
  -- the run never faults (run_safe)
  obtain ⟨last, accesses, hr, _, _⟩ := run_safe hvalid initial_invariant roundRobin_valid
  -- every thread gets enough turns, so every thread finishes
  have hd : completed cfg last = true :=
    completed_eq_true.mpr (sufficiently_scheduled_finishes hvalid roundRobin_valid hr
      (fun _ ht => Nat.le_of_eq (roundRobin_count ht).symm))
  -- a finished run is correct and safe (completed_execution_correct)
  exact ⟨last, accesses, hr, hd, completed_execution_correct hvalid roundRobin_valid hr hd⟩

end Keystone.GPU

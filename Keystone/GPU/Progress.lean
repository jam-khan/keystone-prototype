import Keystone.GPU.Proofs

namespace Keystone.GPU

/-- Instructions left for a real thread. A padded thread can finish sooner. -/
def Instr.remaining : Instr → Nat
  | .guard => 6
  | .page => 5
  | .table => 4
  | .kvIndex => 3
  | .load => 2
  | .store => 1
  | .done => 0

@[simp] theorem Instr.remaining_eq_zero (instr : Instr) :
    instr.remaining = 0 ↔ instr = .done := by
  cases instr <;> simp [Instr.remaining]

private theorem step_remaining (ht : tid < cfg.numThreads)
    (hs : step cfg mem tid s = .ok (next, access)) (j : Nat) :
    (next.threads j).instr.remaining ≤
      (s.threads j).instr.remaining - if j = tid then 1 else 0 := by
  cases hp : (s.threads tid).instr <;>
    simp [step, Nat.not_le_of_gt ht, hp] at hs
  all_goals try split at hs
  all_goals try cases hs
  all_goals by_cases hj : j = tid <;> simp_all [withThread, withOutput, Instr.remaining]

/-- Each scheduled instruction reduces its thread's remaining work; done threads stutter. -/
theorem run_remaining (hschedule : ∀ t ∈ schedule, t < cfg.numThreads)
    (hrun : run cfg mem schedule s = .ok (last, accesses)) (j : Nat) :
    (last.threads j).instr.remaining ≤
      (s.threads j).instr.remaining - schedule.count j := by
  induction schedule generalizing s accesses with
  | nil =>
    cases hrun
    simp
  | cons tid schedule ih =>
    have ht : tid < cfg.numThreads := hschedule tid (by simp)
    cases hs : step cfg mem tid s with
    | error e =>
      simp [run, hs] at hrun
      cases hrun
    | ok pair =>
      obtain ⟨next, access⟩ := pair
      simp only [run, hs] at hrun
      change (do let v ← run cfg mem schedule next
                 pure (v.1, access.toList ++ v.2)) = Except.ok (last, accesses) at hrun
      cases hr : run cfg mem schedule next with
      | error e =>
        simp [hr] at hrun
        cases hrun
      | ok pair =>
        obtain ⟨last', accesses'⟩ := pair
        simp only [hr] at hrun
        cases hrun
        have hind := ih (fun t ht => hschedule t (by simp [ht])) hr
        have hstep := step_remaining ht hs j
        by_cases hj : j = tid
        · subst j
          simp at *
          omega
        · have hj' : tid ≠ j := Ne.symm hj
          simp [hj, hj'] at *
          omega

theorem sufficiently_scheduled_finishes (hschedule : ∀ t ∈ schedule, t < cfg.numThreads)
    (hrun : run cfg mem schedule initialState = .ok (last, accesses))
    (hcount : ∀ t, t < cfg.numThreads → 6 ≤ schedule.count t) : Finished cfg last := by
  intro t ht
  have hr := run_remaining hschedule hrun t
  have hc := hcount t ht
  change (last.threads t).instr.remaining ≤ 6 - schedule.count t at hr
  exact (Instr.remaining_eq_zero _).mp (by omega)

private theorem roundRobin_valid : ∀ t ∈ roundRobin cfg, t < cfg.numThreads := by
  simp [roundRobin]

private theorem roundRobin_count (ht : tid < cfg.numThreads) :
    (roundRobin cfg).count tid = 6 := by
  simp [roundRobin, List.replicate_succ, List.count_range, ht]

/-- Six complete rounds finish every thread without a fairness assumption. -/
theorem roundRobin_finishes
    (hrun : run cfg mem (roundRobin cfg) initialState = .ok (last, accesses)) :
    completed cfg last = true := by
  apply completed_eq_true.mpr
  apply sufficiently_scheduled_finishes roundRobin_valid hrun
  intro t ht
  simp [roundRobin_count ht]

theorem verified_roundRobin (hvalid : ValidLaunch cfg mem) :
    ∃ last accesses,
      run cfg mem (roundRobin cfg) initialState = .ok (last, accesses) ∧
      completed cfg last = true ∧
      (∀ t, t < cfg.numTokens → last.output t = some (expectedEntry cfg mem t)) ∧
      (∀ a ∈ accesses, AccessSafe cfg mem a) := by
  obtain ⟨last, accesses, hr, hi, ha⟩ :=
    run_safe hvalid initial_invariant roundRobin_valid
  have hd := roundRobin_finishes hr
  exact ⟨last, accesses, hr, hd,
    fun _ ht => finished_correct hvalid hi (completed_eq_true.mp hd) ht, ha⟩

end Keystone.GPU

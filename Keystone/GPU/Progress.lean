import Keystone.GPU.Proofs

namespace Keystone.GPU

/-- Remaining instructions for an active lane. A padded lane can finish sooner. -/
def PC.remaining : PC → Nat
  | .guard => 6
  | .index => 5
  | .table => 4
  | .address => 3
  | .load => 2
  | .store => 1
  | .done => 0

@[simp] theorem PC.remaining_eq_zero (pc : PC) : pc.remaining = 0 ↔ pc = .done := by
  cases pc <;> simp [PC.remaining]

private theorem step_remaining (ht : tid < cfg.lanes)
    (hs : step .gather cfg input tid m = .ok (next, access)) (j : Nat) :
    (next.threads j).pc.remaining ≤
      (m.threads j).pc.remaining - if j = tid then 1 else 0 := by
  cases hp : (m.threads tid).pc <;>
    simp [step, Nat.not_le_of_gt ht, hp] at hs
  all_goals try split at hs
  all_goals try cases hs
  all_goals by_cases hj : j = tid <;> simp_all [withLane, withOutput, PC.remaining]

/-- Each scheduled instruction reduces its lane’s remaining work; done lanes stutter. -/
theorem run_remaining (hschedule : ∀ t ∈ schedule, t < cfg.lanes)
    (hrun : run .gather cfg input schedule m = .ok (last, accesses)) (j : Nat) :
    (last.threads j).pc.remaining ≤
      (m.threads j).pc.remaining - schedule.count j := by
  induction schedule generalizing m accesses with
  | nil =>
    cases hrun
    simp
  | cons tid schedule ih =>
    have ht : tid < cfg.lanes := hschedule tid (by simp)
    cases hs : step .gather cfg input tid m with
    | error e =>
      simp [run, hs] at hrun
      cases hrun
    | ok pair =>
      obtain ⟨next, access⟩ := pair
      simp only [run, hs] at hrun
      change (do let v ← run .gather cfg input schedule next
                 pure (v.1, access.toList ++ v.2)) = Except.ok (last, accesses) at hrun
      cases hr : run .gather cfg input schedule next with
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

theorem sufficiently_scheduled_finishes (hschedule : ∀ t ∈ schedule, t < cfg.lanes)
    (hrun : run .gather cfg input schedule init = .ok (last, accesses))
    (hcount : ∀ t, t < cfg.lanes → 6 ≤ schedule.count t) : Finished cfg last := by
  intro t ht
  have hr := run_remaining hschedule hrun t
  have hc := hcount t ht
  change (last.threads t).pc.remaining ≤ 6 - schedule.count t at hr
  exact (PC.remaining_eq_zero _).mp (by omega)

private theorem roundRobin_valid : ∀ t ∈ roundRobin cfg, t < cfg.lanes := by
  simp [roundRobin]

private theorem roundRobin_count (ht : tid < cfg.lanes) :
    (roundRobin cfg).count tid = 6 := by
  simp [roundRobin, List.replicate_succ, List.count_range, ht]

/-- Six complete rounds finish every lane without a fairness assumption. -/
theorem roundRobin_finishes
    (hrun : run .gather cfg input (roundRobin cfg) init = .ok (last, accesses)) :
    completed cfg last = true := by
  apply completed_eq_true.mpr
  apply sufficiently_scheduled_finishes roundRobin_valid hrun
  intro t ht
  simp [roundRobin_count ht]

theorem verified_roundRobin (hvalid : ValidInput cfg input) :
    ∃ last accesses,
      run .gather cfg input (roundRobin cfg) init = .ok (last, accesses) ∧
      completed cfg last = true ∧
      (∀ t, t < cfg.n → last.output t = some (referenceAt cfg input t)) ∧
      (∀ a ∈ accesses, AccessSafe cfg input a) := by
  obtain ⟨last, accesses, hr, hi, ha⟩ :=
    run_safe hvalid initial_invariant roundRobin_valid
  have hd := roundRobin_finishes hr
  exact ⟨last, accesses, hr, hd,
    fun _ ht => finished_correct hvalid hi (completed_eq_true.mp hd) ht, ha⟩

end Keystone.GPU

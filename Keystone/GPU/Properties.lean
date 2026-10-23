import Keystone.GPU.KVGather -- Kernel model and schedules.
import Keystone.GPU.Auxiliary -- Invariant and supporting proofs.

/-!
# Properties: what is proved about the KV gather

1. `run_safe`: on a valid launch, any schedule of launched threads runs without
   faulting, so every access is in bounds.
2. `completed_execution_correct`: once every thread is done, output = `expectedOutput`.
3. `run_stores_distinct`: no output slot is written twice, so no two writes race.
4. `sufficiently_scheduled_finishes`: `6 * numRounds + 1` turns per thread finish every thread.
5. `verified_roundRobin`: on a valid launch, `roundRobin` runs safely, finishes,
   and outputs `expectedOutput`.

The invariant (`ThreadOK`, `Invariant`) and the helper lemmas are in `Auxiliary.lean`.
-/

namespace Keystone.GPU

/-! ## Safety: no step faults, every access is in bounds -/

/-- An access is inside the buffer it touches. -/
def AccessSafe (cfg : Config) (mem : KVMemory) (a : Access) : Prop :=
  match a.buffer with
  | .pageTable => a.index < mem.pageTable.size
  | .kvCache   => a.index < mem.kvCache.size
  | .output    => a.index < cfg.numTokens

-- `step` checks each bound before it accesses, so any access it returns is in bounds
private theorem step_access_safe (ht : tid < cfg.numThreads)
    (hs : step cfg mem tid s = .ok (next, some a)) : AccessSafe cfg mem a := by
  cases hp : (s.threads tid).instr <;>
    simp [step, Nat.not_le_of_gt ht, hp] at hs
  all_goals try split at hs
  all_goals try cases hs
  all_goals simp_all [AccessSafe]

/-- Any schedule of launched threads runs without faulting, so every access is in bounds.
It need not finish. -/
theorem run_safe (hvalid : ValidLaunch cfg mem) (hinv : Invariant cfg mem s)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads) :
    ∃ last accesses, run cfg mem schedule s = .ok (last, accesses) ∧
      Invariant cfg mem last ∧ ∀ a ∈ accesses, AccessSafe cfg mem a := by
  induction schedule generalizing s with
  | nil => exact ⟨s, [], rfl, hinv, by simp⟩
  | cons tid schedule ih =>
    -- first step is safe (step_safe), the rest by induction
    have ht : tid < cfg.numThreads := hschedule tid (by simp)
    obtain ⟨next, access, hstep, hnext⟩ := step_safe hvalid hinv ht
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
          exact step_access_safe ht hstep
      · exact has a hright

/-! ## Correctness: a finished run produces the expected output -/

/-- Every launched thread is at `.done`. -/
def Finished (cfg : Config) (s : KernelState) : Prop :=
  ∀ tid, tid < cfg.numThreads → (s.threads tid).instr = .done

@[simp] theorem completed_eq_true : completed cfg s = true ↔ Finished cfg s := by
  simp [completed, Finished, List.all_eq_true]

/-- For ANY schedule that finishes: output matches the spec, and every access was safe. -/
theorem completed_execution_correct (hvalid : ValidLaunch cfg mem)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads)
    (hrun : run cfg mem schedule initialState = .ok (last, accesses))
    (hdone : completed cfg last = true) :
    (∀ t, t < cfg.numTokens → last.output t = some (expectedEntry cfg mem t)) ∧
    (∀ a ∈ accesses, AccessSafe cfg mem a) := by
  obtain ⟨last', accesses', hr, hi, ha⟩ := run_safe hvalid initial_invariant hschedule
  rw [hrun] at hr
  cases hr
  exact ⟨fun _ ht => finished_correct hvalid hi (completed_eq_true.mp hdone) ht, ha⟩

/-! ## Race freedom: no output slot is ever written twice -/

/-- In any run, no output slot is written twice:
not by two threads, and not by one thread in two different rounds. -/
theorem run_stores_distinct (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads)
    (hrun : run cfg mem schedule s = .ok (last, accesses)) :
    accesses.Pairwise (fun a b => a.buffer = .output → b.buffer = .output → a.index ≠ b.index) :=
  (run_stores_fresh hschedule hrun).2

/-! ## Progress: every thread finishes

Safety alone allows a thread that is never scheduled to stay unfinished forever.
Each thread's countdown `remaining` drops by 1 per turn and is 0 only at `.done`. -/

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

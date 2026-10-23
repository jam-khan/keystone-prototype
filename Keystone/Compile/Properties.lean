import Keystone.GPU.KVGather -- Source step/run and kernel state.
import Keystone.GPU.Proofs.Kernel -- GPU.Invariant used by run_safe.
import Keystone.GPU.Properties -- The five GPU guarantees being transferred.
import Keystone.Compile.Compiler -- Compiled step/run.
import Keystone.Compile.Proofs.Compiler -- Each selected block executes its source stage.

namespace Keystone.Compile

/-- Each compiled block has exactly the effect of the original GPU instruction.
This includes faults and arbitrary intermediate states, not just valid launches. -/
theorem step_eq
  (cfg : GPU.Config)
  (mem : GPU.KVMemory)
  (tid : Nat)
  (s : GPU.KernelState) :
    step cfg mem tid s =
    (GPU.step cfg mem tid s).map
      (fun (next, access) => (next, access.toList)) := by
  by_cases ht : tid ≥ cfg.numThreads
  · simp [step, GPU.step, ht] <;> rfl
  · simpa only [step, ite_eq_right ht] using
      execute_compiled_block cfg mem tid s (Nat.lt_of_not_ge ht)

/-- Every schedule produces the same full state, access trace, or fault. -/
theorem run_eq
  (cfg : GPU.Config) (mem : GPU.KVMemory) (schedule : List Nat) (s : GPU.KernelState) :
    run cfg mem schedule s = GPU.run cfg mem schedule s := by
  induction schedule generalizing s with
  | nil => rfl
  | cons tid schedule ih =>
    simp only [run, step_eq, GPU.run]
    cases GPU.step cfg mem tid s with
    | error fault => rfl
    | ok pair =>
      obtain ⟨next, access⟩ := pair
      change (do let (last, accesses) ← run cfg mem schedule next
                 pure (last, access.toList ++ accesses)) =
             (do let (last, accesses) ← GPU.run cfg mem schedule next
                 pure (last, access.toList ++ accesses))
      rw [ih]

-- Reuse the five GPU proofs. No new output specification or safety invariant.

theorem run_safe
  (hvalid : GPU.ValidLaunch cfg mem)
  (hinv   : GPU.Invariant cfg mem s)
  (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads) :
    ∃ last accesses, run cfg mem schedule s = .ok (last, accesses) ∧
      GPU.Invariant cfg mem last ∧ ∀ a ∈ accesses, GPU.AccessSafe cfg mem a := by
  rw [run_eq]
  exact GPU.run_safe hvalid hinv hschedule

theorem completed_execution_correct (hvalid : GPU.ValidLaunch cfg mem)
    (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads)
    (hrun : run cfg mem schedule GPU.initialState = .ok (last, accesses))
    (hdone : GPU.completed cfg last = true) :
    (∀ t, t < cfg.numTokens → last.output t = some (GPU.expectedEntry cfg mem t)) ∧
    (∀ a ∈ accesses, GPU.AccessSafe cfg mem a) := by
  rw [run_eq] at hrun
  exact GPU.completed_execution_correct hvalid hschedule hrun hdone

theorem run_stores_distinct (hschedule : ∀ tid ∈ schedule, tid < cfg.numThreads)
    (hrun : run cfg mem schedule s = .ok (last, accesses)) :
    accesses.Pairwise (fun a b =>
      a.buffer = .output → b.buffer = .output → a.index ≠ b.index) := by
  rw [run_eq] at hrun
  exact GPU.run_stores_distinct hschedule hrun

theorem sufficiently_scheduled_finishes (hvalid : GPU.ValidLaunch cfg mem)
    (hschedule : ∀ t ∈ schedule, t < cfg.numThreads)
    (hrun : run cfg mem schedule GPU.initialState = .ok (last, accesses))
    (hcount : ∀ t, t < cfg.numThreads → 6 * GPU.numRounds cfg + 1 ≤ schedule.count t) :
    GPU.Finished cfg last := by
  rw [run_eq] at hrun
  exact GPU.sufficiently_scheduled_finishes hvalid hschedule hrun hcount

theorem verified_roundRobin (hvalid : GPU.ValidLaunch cfg mem) :
    ∃ last accesses,
      run cfg mem (GPU.roundRobin cfg) GPU.initialState = .ok (last, accesses) ∧
      GPU.completed cfg last = true ∧
      (∀ t, t < cfg.numTokens → last.output t = some (GPU.expectedEntry cfg mem t)) ∧
      (∀ a ∈ accesses, GPU.AccessSafe cfg mem a) := by
  rw [run_eq]
  exact GPU.verified_roundRobin hvalid

end Keystone.Compile

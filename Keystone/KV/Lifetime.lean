import Keystone.KV.Controller

/-! Controller histories, lease retention, and conditional reclamation. -/
namespace Keystone.KV

inductive Action where
  | allocate (owner : Nat)
  | submit (owner : Nat) (pages : List Lease)
  | retire (owner : Nat)
  | complete (ticket : Nat)
  deriving Repr, DecidableEq

/-- State transitions for histories; rejected commands leave the state unchanged. -/
def step (s : State) : Action → State
  | .allocate owner => (allocate s owner).map Prod.fst |>.getD s
  | .submit owner pages => (submit s owner pages).map Prod.fst |>.getD s
  | .retire owner => retire s owner
  | .complete ticket => complete s ticket

def run (s : State) : List Action → State
  | [] => s
  | action :: rest => run (step s action) rest

theorem step_valid (h : Valid s) (action : Action) : Valid (step s action) := by
  cases action with
  | allocate owner =>
    simp only [step]
    cases result : allocate s owner with
    | none => exact h
    | some pair => exact allocate_valid h result
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => exact h
    | some pair => exact submit_valid h result
  | retire owner => exact retire_valid h
  | complete ticket => exact complete_valid ticket h

theorem run_valid (h : Valid s) (actions : List Action) : Valid (run s actions) := by
  induction actions generalizing s with
  | nil => exact h
  | cons action rest ih => exact ih (step_valid h action)

/-- Controller operations preserve pool capacity. -/
theorem step_capacity (s : State) (action : Action) :
    (step s action).capacity = s.capacity := by
  cases action with
  | allocate owner =>
    simp only [step]
    cases result : allocate s owner with
    | none => rfl
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      unfold allocate at result
      split at result
      · contradiction
      · cases found : (List.range s.capacity).find? (fun page =>
            !s.allocations.any (fun lease => decide (lease.page = page))) with
        | none => simp [found] at result
        | some page => simp [found] at result; rw [← result]
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => rfl
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      unfold submit at result
      split at result
      · rw [← Option.some.inj result]
      · contradiction
  | retire owner => rfl
  | complete id =>
    change (complete s id).capacity = s.capacity
    unfold complete
    split <;> rfl

theorem run_capacity (s : State) (actions : List Action) :
    (run s actions).capacity = s.capacity := by
  induction actions generalizing s with
  | nil => rfl
  | cons action rest ih => exact (ih _).trans (step_capacity s action)

/-- Every history starting from `init` preserves the controller invariants. -/
theorem reachable_valid (capacity : Nat) (actions : List Action) :
    Valid (run (init capacity) actions) := run_valid (init_valid capacity) actions

@[simp] theorem complete_pending (id : Nat) :
    ticket ∈ (complete s id).pending ↔ ticket ∈ s.pending ∧ ticket.id ≠ id := by
  unfold complete
  split
  · simp [collect]
  · rename_i missing
    constructor
    · intro ht
      exact ⟨ht, fun eq => missing ⟨ticket, ht, eq⟩⟩
    · exact And.left

theorem complete_unknown (id : Nat)
    (missing : ∀ ticket ∈ s.pending, ticket.id ≠ id) : complete s id = s := by
  simp [complete, show ¬ (∃ ticket ∈ s.pending, ticket.id = id) from by
    rintro ⟨ticket, ht, eq⟩; exact missing ticket ht eq]

theorem complete_idempotent (s : State) (id : Nat) :
    complete (complete s id) id = complete s id := by
  apply complete_unknown
  intro ticket ht
  exact (complete_pending id |>.mp ht).2

/-- Retirement leaves pending operations intact. -/
@[simp] theorem retire_pending : (retire s owner).pending = s.pending := rfl

/-- Only the operation’s own completion removes its ticket. -/
theorem pending_step (ht : ticket ∈ s.pending) (action : Action)
    (notCompleted : action ≠ .complete ticket.id) : ticket ∈ (step s action).pending := by
  cases action with
  | allocate owner =>
    simp only [step]
    cases result : allocate s owner with
    | none => exact ht
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      unfold allocate at result
      split at result
      · contradiction
      · cases found : (List.range s.capacity).find? (fun page =>
            !s.allocations.any (fun lease => decide (lease.page = page))) with
        | none => simp [found] at result
        | some page =>
          simp [found] at result
          rw [← result]
          exact ht
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => exact ht
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      unfold submit at result
      split at result
      · have pairEq := Option.some.inj result
        rw [← pairEq]
        exact List.mem_cons_of_mem _ ht
      · contradiction
  | retire owner => exact ht
  | complete id =>
    apply (complete_pending id).mpr
    exact ⟨ht, fun eq => notCompleted (by rw [eq])⟩

theorem pending_run (ht : ticket ∈ s.pending)
    (notCompleted : ∀ action ∈ actions, action ≠ .complete ticket.id) :
    ticket ∈ (run s actions).pending := by
  induction actions generalizing s with
  | nil => exact ht
  | cons action rest ih =>
    apply ih (pending_step ht action (notCompleted action (by simp)))
    intro a ha; exact notCompleted a (List.mem_cons_of_mem _ ha)

/-- The ticket counter is monotone; a new ticket uses its previous value. -/
theorem step_ticket_evolution (s : State) (action : Action) :
    s.nextTicket ≤ (step s action).nextTicket ∧
      ∀ ticket ∈ (step s action).pending, ticket ∈ s.pending ∨ ticket.id = s.nextTicket := by
  cases action with
  | allocate owner =>
    simp only [step]
    cases result : allocate s owner with
    | none => exact ⟨Nat.le_refl _, fun _ ht => Or.inl ht⟩
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      unfold allocate at result
      split at result
      · contradiction
      · cases found : (List.range s.capacity).find? (fun page =>
            !s.allocations.any (fun lease => decide (lease.page = page))) with
        | none => simp [found] at result
        | some page =>
          simp [found] at result
          rw [← result]
          exact ⟨Nat.le_refl _, fun _ ht => Or.inl ht⟩
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => exact ⟨Nat.le_refl _, fun _ ht => Or.inl ht⟩
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      unfold submit at result
      split at result
      · rw [← Option.some.inj result]
        constructor
        · exact Nat.le_succ _
        · intro ticket ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact Or.inr rfl
          · exact Or.inl ht
      · contradiction
  | retire owner => exact ⟨Nat.le_refl _, fun _ ht => Or.inl ht⟩
  | complete id =>
    constructor
    · change s.nextTicket ≤ (complete s id).nextTicket
      unfold complete
      split <;> exact Nat.le_refl _
    · intro ticket ht
      exact Or.inl ((complete_pending id).mp ht).1

/-- Future tickets below the cutoff must already be pending now. -/
theorem old_pending_origin (cutoff : Nat) (bound : cutoff ≤ s.nextTicket)
    (ht : ticket ∈ (run s actions).pending) (old : ticket.id < cutoff) : ticket ∈ s.pending := by
  induction actions generalizing s with
  | nil => exact ht
  | cons action rest ih =>
    have evolution := step_ticket_evolution s action
    have before := ih (Nat.le_trans bound evolution.1) ht
    rcases evolution.2 ticket before with present | fresh
    · exact present
    · omega

@[simp] theorem complete_counter (s : State) (id : Nat) :
    (complete s id).nextTicket = s.nextTicket := by
  unfold complete
  split <;> rfl

/-- A completed ID never returns, so stale completion remains a no-op. -/
theorem completed_ticket_never_reappears (id : Nat) (old : id < s.nextTicket) (actions : List Action) :
    complete (run (complete s id) actions) id = run (complete s id) actions := by
  apply complete_unknown
  intro ticket ht eq
  have origin := old_pending_origin s.nextTicket
    (by simp : s.nextTicket ≤ (complete s id).nextTicket) ht (by omega)
  exact (complete_pending id |>.mp origin).2 eq

/-- The generation counter is monotone; allocation uses its previous value. -/
theorem step_generation_evolution (s : State) (action : Action) :
    s.nextGeneration ≤ (step s action).nextGeneration ∧
      ∀ lease ∈ (step s action).allocations,
        lease ∈ s.allocations ∨ lease.generation = s.nextGeneration := by
  cases action with
  | allocate owner =>
    simp only [step]
    cases result : allocate s owner with
    | none => exact ⟨Nat.le_refl _, fun _ hl => Or.inl hl⟩
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      unfold allocate at result
      split at result
      · contradiction
      · cases found : (List.range s.capacity).find? (fun page =>
            !s.allocations.any (fun lease => decide (lease.page = page))) with
        | none => simp [found] at result
        | some page =>
          simp [found] at result
          rw [← result]
          constructor
          · exact Nat.le_succ _
          · intro lease hl
            rcases List.mem_cons.mp hl with rfl | hl
            · exact Or.inr rfl
            · exact Or.inl hl
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => exact ⟨Nat.le_refl _, fun _ hl => Or.inl hl⟩
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      unfold submit at result
      split at result
      · rw [← Option.some.inj result]
        exact ⟨Nat.le_refl _, fun _ hl => Or.inl hl⟩
      · contradiction
  | retire owner =>
    exact ⟨Nat.le_refl _, fun _ hl => Or.inl (mem_collect.mp hl).1⟩
  | complete id =>
    simp only [step]
    unfold complete
    split
    · exact ⟨Nat.le_refl _, fun _ hl => Or.inl (mem_collect.mp hl).1⟩
    · exact ⟨Nat.le_refl _, fun _ hl => Or.inl hl⟩

/-- Future leases below the cutoff must already be allocated now. -/
theorem old_lease_origin (cutoff : Nat) (bound : cutoff ≤ s.nextGeneration)
    (hl : lease ∈ (run s actions).allocations) (old : lease.generation < cutoff) :
    lease ∈ s.allocations := by
  induction actions generalizing s with
  | nil => exact hl
  | cons action rest ih =>
    have evolution := step_generation_evolution s action
    have before := ih (Nat.le_trans bound evolution.1) hl
    rcases evolution.2 lease before with present | fresh
    · exact present
    · omega

/-- Reclaimed leases stay invalid even after their physical page is reused. -/
theorem reclaimed_lease_never_reappears (old : lease.generation < s.nextGeneration)
    (gone : lease ∉ s.allocations) (actions : List Action) :
    lease ∉ (run s actions).allocations := by
  intro hl
  exact gone (old_lease_origin s.nextGeneration (Nat.le_refl _) hl old)

/-- Pending work retains the exact owner and generation it captured. -/
theorem pending_cannot_reassign (h : Valid s) (ht : ticket ∈ s.pending)
    (hl : lease ∈ ticket.pages) (ho : other ∈ s.allocations)
    (samePage : other.page = lease.page) : other = lease :=
  h.exclusive other ho lease (h.protects ticket ht lease hl) samePage

/-- Until completion, every captured lease remains allocated and exclusive. -/
theorem lifetime_safety (h : Valid s) (ht : ticket ∈ s.pending)
    (hl : lease ∈ ticket.pages)
    (notCompleted : ∀ action ∈ actions, action ≠ .complete ticket.id) :
    lease ∈ (run s actions).allocations ∧
      ∀ other ∈ (run s actions).allocations, other.page = lease.page → other = lease := by
  have finalValid := run_valid h actions
  have stillPending := pending_run ht notCompleted
  exact ⟨finalValid.protects ticket stillPending lease hl,
    fun other ho eq => pending_cannot_reassign finalValid stillPending hl ho eq⟩

/-- The final completion reclaims retired pages; no device liveness is assumed. -/
theorem reclaim_after_last_completion (id : Nat)
    (retired : lease.owner ∈ s.retired)
    (finishing : ∃ ticket ∈ s.pending, ticket.id = id)
    (lastUse : ∀ ticket ∈ s.pending, lease ∈ ticket.pages → ticket.id = id) :
    lease ∉ (complete s id).allocations := by
  simp only [complete, ite_eq_left finishing]
  intro hm
  have live := (mem_collect.mp hm).2
  rcases live with active | ⟨ticket, ht, hl⟩
  · exact active retired
  · have ht' := List.mem_filter.mp ht
    have neq : ticket.id ≠ id := by simpa using ht'.2
    exact neq (lastUse ticket ht'.1 hl)

/-- Retirement immediately reclaims pages unused by pending work. -/
theorem retire_reclaims_unused
    (ownerEq : lease.owner = owner)
    (unused : ∀ ticket ∈ s.pending, lease ∉ ticket.pages) :
    lease ∉ (retire s owner).allocations := by
  intro hm
  have live := (mem_collect.mp hm).2
  rcases live with active | ⟨ticket, ht, hl⟩
  · have retired : lease.owner ∈
        (if owner ∈ s.retired then s.retired else owner :: s.retired) := by
      rw [ownerEq]; split <;> simp_all
    exact active retired
  · exact unused ticket ht hl

/-- Retired owners cannot submit new work. -/
theorem retired_cannot_submit (retired : owner ∈ s.retired) :
    submit s owner pages = none := by
  simp [submit, retired]

/-- Submission rejects stale leases. -/
theorem stale_lease_rejected (hl : lease ∈ pages) (stale : lease ∉ s.allocations) :
    submit s owner pages = none := by
  unfold submit
  split
  · rename_i guard
    exact False.elim (stale (guard.2 lease hl).1)
  · rfl

end Keystone.KV

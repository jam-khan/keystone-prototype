import Keystone.KV.Manager -- Manager operations, invariants, and command histories.

/-! Supporting proofs for manager operations and histories. -/
namespace Keystone.KV

-- Operation invariants.

@[simp] theorem referenced_iff : referenced pending lease = true ↔
    ∃ ticket ∈ pending, lease ∈ ticket.pages := by
  simp [referenced, List.any_eq_true]

@[simp] theorem mem_collect : lease ∈ (collect s).allocations ↔
    lease ∈ s.allocations ∧
      (lease.owner ∉ s.retired ∨ ∃ ticket ∈ s.pending, lease ∈ ticket.pages) := by
  simp [collect]

theorem init_valid (capacity : Nat) : Valid (init capacity) := by
  constructor <;> simp [init]

theorem collect_valid (h : Valid s) : Valid (collect s) := by
  constructor
  · intro lease hm; exact h.bounded lease (mem_collect.mp hm).1
  · intro a ha b hb eq; exact h.exclusive a (mem_collect.mp ha).1 b (mem_collect.mp hb).1 eq
  · intro lease hm; exact h.generations lease (mem_collect.mp hm).1
  · exact h.tickets
  · exact h.uniqueTickets
  · intro ticket ht lease hl
    exact mem_collect.mpr ⟨h.protects ticket ht lease hl, Or.inr ⟨ticket, ht, hl⟩⟩
  · exact h.owned

/-- Successful allocation adds one fresh lease and leaves pending work intact. -/
theorem allocate_success (ok : allocate s owner = some (next, lease)) :
    next = { s with allocations := lease :: s.allocations,
                    nextGeneration := s.nextGeneration + 1 } ∧
    lease.owner = owner ∧ lease.generation = s.nextGeneration ∧
    lease.page < s.capacity ∧
    ∀ old ∈ s.allocations, old.page ≠ lease.page := by
  unfold allocate at ok
  split at ok
  · contradiction
  · cases found : (List.range s.capacity).find? (fun page =>
        !s.allocations.any (fun lease => decide (lease.page = page))) with
    | none => simp [found] at ok
    | some page =>
      simp [found] at ok
      rcases ok with ⟨rfl, rfl⟩
      refine ⟨rfl, rfl, rfl, List.mem_range.mp (List.mem_of_find?_eq_some found), ?_⟩
      simpa [List.any_eq_false] using List.find?_some found

/-- Submission changes only pending work and its counter; pages keep their order. -/
theorem submit_success (ok : submit s owner pages = some (next, ticket)) :
    next = { s with pending := ticket :: s.pending, nextTicket := s.nextTicket + 1 } ∧
    ticket = ⟨s.nextTicket, owner, pages⟩ ∧
    owner ∉ s.retired ∧ ∀ lease ∈ pages, lease ∈ s.allocations ∧ lease.owner = owner := by
  unfold submit at ok
  split at ok
  · rename_i guard
    obtain ⟨rfl, rfl⟩ := Option.some.inj ok
    exact ⟨rfl, rfl, guard⟩
  · contradiction

theorem allocate_valid (h : Valid s) (ok : allocate s owner = some (next, lease)) :
    Valid next := by
  obtain ⟨rfl, _, generation, bound, free⟩ := allocate_success ok
  constructor
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact bound
    · exact h.bounded a ha
  · intro a ha b hb eq
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact False.elim (free b hb eq.symm)
    · exact False.elim (free a ha eq)
    · exact h.exclusive a ha b hb eq
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [generation]
    · exact Nat.lt_succ_of_lt (h.generations a ha)
  · exact h.tickets
  · exact h.uniqueTickets
  · intro t ht l hl; exact List.mem_cons_of_mem _ (h.protects t ht l hl)
  · exact h.owned

theorem submit_valid (h : Valid s) (ok : submit s owner pages = some (next, ticket)) :
    Valid next := by
  obtain ⟨rfl, rfl, _, captured⟩ := submit_success ok
  constructor
  · exact h.bounded
  · exact h.exclusive
  · exact h.generations
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (h.tickets t ht)
  · intro a ha b hb eq
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · have := h.tickets b hb; simp only at eq; omega
    · have := h.tickets a ha; simp only at eq; omega
    · exact h.uniqueTickets a ha b hb eq
  · intro t ht l hl
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (captured l hl).1
    · exact h.protects t ht l hl
  · intro t ht l hl
    rcases List.mem_cons.mp ht with rfl | ht
    · exact (captured l hl).2
    · exact h.owned t ht l hl

theorem retire_valid (h : Valid s) : Valid (retire s owner) := by
  apply collect_valid
  exact ⟨h.bounded, h.exclusive, h.generations, h.tickets, h.uniqueTickets, h.protects, h.owned⟩

theorem complete_valid (id : Nat) (h : Valid s) : Valid (complete s id) := by
  unfold complete
  split
  · apply collect_valid
    constructor
    · exact h.bounded
    · exact h.exclusive
    · exact h.generations
    · intro t ht; exact h.tickets t (List.mem_filter.mp ht).1
    · intro a ha b hb eq
      exact h.uniqueTickets a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 eq
    · intro t ht; exact h.protects t (List.mem_filter.mp ht).1
    · intro t ht; exact h.owned t (List.mem_filter.mp ht).1
  · exact h

-- Histories, pending tickets, and stale handles.

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

/-- Manager operations preserve pool capacity. -/
theorem step_capacity (s : State) (action : Action) :
    (step s action).capacity = s.capacity := by
  cases action with
  | allocate owner =>
    simp only [step]
    cases result : allocate s owner with
    | none => rfl
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      rw [(allocate_success result).1]
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => rfl
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      rw [(submit_success result).1]
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

/-- Every history starting from `init` preserves the manager invariants. -/
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
      rw [(allocate_success result).1]
      exact ht
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => exact ht
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      rw [(submit_success result).1]
      exact List.mem_cons_of_mem _ ht
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
      rw [(allocate_success result).1]
      exact ⟨Nat.le_refl _, fun _ ht => Or.inl ht⟩
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => exact ⟨Nat.le_refl _, fun _ ht => Or.inl ht⟩
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      rw [(submit_success result).1, (submit_success result).2.1]
      constructor
      · exact Nat.le_succ _
      · intro ticket ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inr rfl
        · exact Or.inl ht
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
      rw [(allocate_success result).1]
      constructor
      · exact Nat.le_succ _
      · intro lease hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Or.inr (allocate_success result).2.2.1
        · exact Or.inl hl
  | submit owner pages =>
    simp only [step]
    cases result : submit s owner pages with
    | none => exact ⟨Nat.le_refl _, fun _ hl => Or.inl hl⟩
    | some pair =>
      simp only [Option.map_some, Option.getD_some]
      rw [(submit_success result).1]
      exact ⟨Nat.le_refl _, fun _ hl => Or.inl hl⟩
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

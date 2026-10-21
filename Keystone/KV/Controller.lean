import Std

/-!
Private-page lifetimes under atomic host commands and truthful completion events.
Completion means all device accesses by that operation have ceased.
Pages are assumed sealed while pending; content stability and driver behavior are
outside this model. Request IDs are not reused; counters are unbounded naturals.
-/
namespace Keystone.KV

structure Lease where
  page : Nat
  owner : Nat
  generation : Nat
  deriving Repr, DecidableEq

structure Ticket where
  id : Nat
  owner : Nat
  pages : List Lease
  deriving Repr, DecidableEq

structure State where
  capacity : Nat
  allocations : List Lease := []
  pending : List Ticket := []
  retired : List Nat := []
  nextGeneration : Nat := 0
  nextTicket : Nat := 0
  deriving Repr, DecidableEq

def init (capacity : Nat) : State := { capacity }

/-- Whether an outstanding operation captures this exact allocation. -/
def referenced (pending : List Ticket) (lease : Lease) : Bool :=
  pending.any fun ticket => decide (lease ∈ ticket.pages)

/-- Retain active owners’ pages and any lease still referenced by pending work. -/
def collect (s : State) : State :=
  { s with allocations := s.allocations.filter fun lease =>
      decide (lease.owner ∉ s.retired) || referenced s.pending lease }

/-- First-free allocation; retired owners cannot restart. -/
def allocate (s : State) (owner : Nat) : Option (State × Lease) := do
  if owner ∈ s.retired then none else
  let page ← (List.range s.capacity).find? fun page =>
    !s.allocations.any (fun lease => decide (lease.page = page))
  let lease : Lease := ⟨page, owner, s.nextGeneration⟩
  pure ({ s with allocations := lease :: s.allocations,
                 nextGeneration := s.nextGeneration + 1 }, lease)

/-- Capture an ordered list of exact live leases; repeated pages are allowed. -/
def submit (s : State) (owner : Nat) (pages : List Lease) : Option (State × Ticket) :=
  if owner ∉ s.retired ∧ ∀ lease ∈ pages, lease ∈ s.allocations ∧ lease.owner = owner then
    let ticket : Ticket := ⟨s.nextTicket, owner, pages⟩
    some ({ s with pending := ticket :: s.pending, nextTicket := s.nextTicket + 1 }, ticket)
  else none

/-- Forbid new work and reclaim unused pages; pending work keeps its leases. -/
def retire (s : State) (owner : Nat) : State :=
  collect { s with retired := if owner ∈ s.retired then s.retired else owner :: s.retired }

/-- Remove the matching ticket and collect; unknown or stale IDs are no-ops. -/
def complete (s : State) (id : Nat) : State :=
  if ∃ ticket ∈ s.pending, ticket.id = id then
    collect { s with pending := s.pending.filter fun ticket => decide (ticket.id ≠ id) }
  else s

/-- Ownership and lifetime invariants preserved by the controller. -/
structure Valid (s : State) : Prop where
  bounded : ∀ lease ∈ s.allocations, lease.page < s.capacity
  exclusive : ∀ a ∈ s.allocations, ∀ b ∈ s.allocations, a.page = b.page → a = b
  generations : ∀ lease ∈ s.allocations, lease.generation < s.nextGeneration
  tickets : ∀ ticket ∈ s.pending, ticket.id < s.nextTicket
  uniqueTickets : ∀ a ∈ s.pending, ∀ b ∈ s.pending, a.id = b.id → a = b
  protects : ∀ ticket ∈ s.pending, ∀ lease ∈ ticket.pages, lease ∈ s.allocations
  owned : ∀ ticket ∈ s.pending, ∀ lease ∈ ticket.pages, lease.owner = ticket.owner

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

theorem allocate_valid (h : Valid s) (ok : allocate s owner = some (next, lease)) :
    Valid next := by
  unfold allocate at ok
  split at ok
  · contradiction
  · rename_i active
    cases found : (List.range s.capacity).find? (fun page =>
        !s.allocations.any (fun lease => decide (lease.page = page))) with
    | none => simp [found] at ok
    | some page =>
      simp [found] at ok
      rcases ok with ⟨rfl, rfl⟩
      have bound := List.mem_range.mp (List.mem_of_find?_eq_some found)
      have free : ∀ lease ∈ s.allocations, lease.page ≠ page := by
        have hf := List.find?_some found
        simpa [List.any_eq_false] using hf
      constructor
      · intro a ha
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
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
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (h.generations a ha)
      · exact h.tickets
      · exact h.uniqueTickets
      · intro t ht l hl; exact List.mem_cons_of_mem _ (h.protects t ht l hl)
      · exact h.owned

theorem submit_valid (h : Valid s) (ok : submit s owner pages = some (next, ticket)) :
    Valid next := by
  unfold submit at ok
  split at ok
  · rename_i guard
    obtain ⟨rfl, rfl⟩ := Option.some.inj ok
    constructor
    · exact h.bounded
    · exact h.exclusive
    · exact h.generations
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
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
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact (guard.2 l hl).1
      · exact h.protects t ht l hl
    · intro t ht l hl
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact (guard.2 l hl).2
      · exact h.owned t ht l hl
  · contradiction

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

end Keystone.KV

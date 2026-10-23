import Std

/-!
Private pages for asynchronous GPU work. Cancellation retires the owner;
pending tickets keep pages allocated until completion. Host commands are atomic,
request IDs are never reused, and counters are unbounded naturals.
-/
namespace Keystone.KV

/-- Page 7 allocated to request 2 at generation 9: `⟨7, 2, 9⟩`. -/
structure Lease where
  page : Nat
  owner : Nat
  generation : Nat
  deriving Repr, DecidableEq

/-- One GPU operation and its ordered page table, captured as exact leases. -/
structure Ticket where
  id : Nat
  owner : Nat
  pages : List Lease
  deriving Repr, DecidableEq

/-- A fixed-size pool, its live allocations, and outstanding GPU operations. -/
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

/-- Ownership and lifetime invariants preserved by the manager. -/
structure Valid (s : State) : Prop where
  bounded : ∀ lease ∈ s.allocations, lease.page < s.capacity
  exclusive : ∀ a ∈ s.allocations, ∀ b ∈ s.allocations, a.page = b.page → a = b
  generations : ∀ lease ∈ s.allocations, lease.generation < s.nextGeneration
  tickets : ∀ ticket ∈ s.pending, ticket.id < s.nextTicket
  uniqueTickets : ∀ a ∈ s.pending, ∀ b ∈ s.pending, a.id = b.id → a = b
  protects : ∀ ticket ∈ s.pending, ∀ lease ∈ ticket.pages, lease ∈ s.allocations
  owned : ∀ ticket ∈ s.pending, ∀ lease ∈ ticket.pages, lease.owner = ticket.owner

/-- Manager command histories used by the lifetime guarantees. -/
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

end Keystone.KV

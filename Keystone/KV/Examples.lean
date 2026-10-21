import Keystone.KV.Lifetime

/-! Kernel-checked examples and constructed faulty policies; no real engine bug is claimed.
-/
namespace Keystone.KV

/-- States of the cancellation, reverse-completion, and page-reuse example. -/
structure Scenario where
  leaseA : Lease
  leaseB : Lease
  first : Ticket
  second : Ticket
  launched : State
  canceled : State
  secondDone : State
  allDone : State
  reused : State
  duplicateDone : State
  deriving Repr, DecidableEq

/-- One page, two readers, and reuse after reverse-order completions. -/
def scenario : Option Scenario := do
  let (s, a) ← allocate (init 1) 10
  let (s, first) ← submit s 10 [a]
  let (launched, second) ← submit s 10 [a]
  let canceled := retire launched 10
  let secondDone := complete canceled second.id
  let allDone := complete secondDone first.id
  let (reused, b) ← allocate allDone 20
  pure ⟨a, b, first, second, launched, canceled, secondDone, allDone,
    reused, complete reused first.id⟩

/-- `scenario_succeeds` rules out this accessor’s fallback. -/
def demo : Scenario := scenario.getD
  ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, []⟩, ⟨0, 0, []⟩,
    init 0, init 0, init 0, init 0, init 0, init 0⟩

theorem scenario_succeeds : scenario = some demo := by decide

theorem cancellation_keeps_both_operations :
    demo.canceled.pending = [demo.second, demo.first] ∧
      demo.leaseA ∈ demo.canceled.allocations := by decide

theorem first_completion_is_insufficient :
    demo.leaseA ∈ demo.secondDone.allocations ∧
      allocate demo.secondDone 20 = none := by decide

theorem last_completion_reclaims : demo.allDone.allocations = [] := by decide

theorem page_reused_with_fresh_generation :
    demo.leaseA.page = demo.leaseB.page ∧
      demo.leaseA.generation ≠ demo.leaseB.generation := by decide

theorem duplicate_completion_is_harmless : demo.duplicateDone = demo.reused := by decide

theorem old_request_cannot_restart : allocate demo.reused 10 = none := by decide

theorem stale_lease_cannot_launch : submit demo.reused 20 [demo.leaseA] = none := by decide

/-- Faulty policy: free on cancellation before device completion. -/
def brokenImmediateFree (s : State) (owner : Nat) : State :=
  { s with allocations := s.allocations.filter fun lease => decide (lease.owner ≠ owner) }

def immediateReuse : Option (State × Lease) :=
  allocate (brokenImmediateFree demo.launched 10) 20

theorem immediate_reuse_violates_lifetime :
    ∃ s b, immediateReuse = some (s, b) ∧ demo.first ∈ s.pending ∧
      demo.leaseA ∉ s.allocations ∧ b.page = demo.leaseA.page ∧ b.owner ≠ demo.leaseA.owner := by
  exact ⟨(immediateReuse.getD (init 0, ⟨0, 0, 0⟩)).1,
    (immediateReuse.getD (init 0, ⟨0, 0, 0⟩)).2, by decide⟩

/-- Faulty policy: free by page number, ignoring operation and generation. -/
def brokenCompleteByPage (s : State) (page : Nat) : State :=
  { s with allocations := s.allocations.filter fun lease => decide (lease.page ≠ page) }

def newLaunch : Option (State × Ticket) := submit demo.reused 20 [demo.leaseB]

theorem stale_completion_violates_lifetime :
    ∃ s ticket, newLaunch = some (s, ticket) ∧
      ticket ∈ (brokenCompleteByPage s demo.leaseA.page).pending ∧
      demo.leaseB ∈ ticket.pages ∧
      demo.leaseB ∉ (brokenCompleteByPage s demo.leaseA.page).allocations := by
  exact ⟨(newLaunch.getD (init 0, ⟨0, 0, []⟩)).1,
    (newLaunch.getD (init 0, ⟨0, 0, []⟩)).2, by decide⟩

/-- An ordered snapshot with two pages and a repeated page. -/
def multiPage : Option (State × Ticket) := do
  let (s, a) ← allocate (init 2) 30
  let (s, b) ← allocate s 30
  let (s, ticket) ← submit s 30 [b, a, b]
  pure (retire s 30, ticket)

theorem multi_page_snapshot_preserves_order :
    (multiPage.map fun (_, ticket) => ticket.pages.map Lease.page) = some [1, 0, 1] := by decide

theorem multi_page_completion_reclaims_all :
    (multiPage.map fun (s, ticket) => (complete s ticket.id).allocations) = some [] := by decide

end Keystone.KV

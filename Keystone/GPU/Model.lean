import Std

namespace Keystone.GPU

/-- Natural-number addresses; `lanes` includes padding. Inputs are immutable
and separate from output. -/
structure Config where
  n : Nat
  pageSize : Nat
  lanes : Nat
  deriving Repr, DecidableEq

structure Input where
  pageTable : Array Nat
  cache : Array UInt32
  deriving Repr, DecidableEq

inductive PC where
  | guard | index | table | address | load | store | done
  deriving Repr, DecidableEq

/-- Register meanings are proved by `LaneOK`, not checked at runtime. -/
structure Lane where
  pc : PC := .guard
  page : Nat := 0
  physical : Nat := 0
  address : Nat := 0
  value : UInt32 := 0
  deriving Repr, DecidableEq

structure Machine where
  threads : Nat → Lane
  output : Nat → Option UInt32

inductive Program where
  | gather | missingMask | wrongPage
  deriving Repr, DecidableEq

inductive Space where
  | pageTable | cache | output
  deriving Repr, DecidableEq

structure Access where
  lane : Nat
  space : Space
  address : Nat
  deriving Repr, DecidableEq

inductive Fault where
  | invalidLane (lane : Nat)
  | outOfBounds (access : Access)
  deriving Repr, DecidableEq

def init : Machine := ⟨fun _ => {}, fun _ => none⟩

def withLane (m : Machine) (tid : Nat) (l : Lane) : Machine :=
  { m with threads := fun j => if j = tid then l else m.threads j }

def withOutput (m : Machine) (tid : Nat) (value : UInt32) : Machine :=
  { m with output := fun j => if j = tid then some value else m.output j }

def physicalPage (input : Input) (page : Nat) : Nat :=
  input.pageTable[page]!

def gatherAddress (cfg : Config) (input : Input) (tid : Nat) : Nat :=
  physicalPage input (tid / cfg.pageSize) * cfg.pageSize + tid % cfg.pageSize

def referenceAt (cfg : Config) (input : Input) (tid : Nat) : UInt32 :=
  input.cache[gatherAddress cfg input tid]!

def reference (cfg : Config) (input : Input) : Array UInt32 :=
  Array.ofFn (fun t : Fin cfg.n => referenceAt cfg input t)

/-- One lane instruction, with bounds checks and access events. Mutations use
the same interpreter. -/
def step (program : Program) (cfg : Config) (input : Input)
    (tid : Nat) (m : Machine) : Except Fault (Machine × Option Access) := do
  if tid ≥ cfg.lanes then throw (.invalidLane tid)
  let l := m.threads tid
  match l.pc with
  | .guard =>
    let active := program == .missingMask || tid < cfg.n
    return (withLane m tid { l with pc := if active then .index else .done }, none)
  | .index =>
    let page := if program == .wrongPage then tid % cfg.pageSize else tid / cfg.pageSize
    return (withLane m tid { l with pc := .table, page := page }, none)
  | .table =>
    let a : Access := ⟨tid, .pageTable, l.page⟩
    if l.page < input.pageTable.size then
      return (withLane m tid { l with pc := .address, physical := physicalPage input l.page }, some a)
    else throw (.outOfBounds a)
  | .address =>
    return (withLane m tid { l with pc := .load, address := l.physical * cfg.pageSize + tid % cfg.pageSize }, none)
  | .load =>
    let a : Access := ⟨tid, .cache, l.address⟩
    if l.address < input.cache.size then
      return (withLane m tid { l with pc := .store, value := input.cache[l.address]! }, some a)
    else throw (.outOfBounds a)
  | .store =>
    let a : Access := ⟨tid, .output, tid⟩
    if tid < cfg.n then
      return (withOutput (withLane m tid { l with pc := .done }) tid l.value, some a)
    else throw (.outOfBounds a)
  | .done => return (m, none)

/-- Replay a supplied interleaving; the schedule need not be fair or complete. -/
def run (program : Program) (cfg : Config) (input : Input) :
    List Nat → Machine → Except Fault (Machine × List Access)
  | [], m => .ok (m, [])
  | tid :: schedule, m => do
    let (next, access) ← step program cfg input tid m
    let (last, accesses) ← run program cfg input schedule next
    return (last, access.toList ++ accesses)

def roundRobin (cfg : Config) : List Nat :=
  (List.replicate 6 (List.range cfg.lanes)).flatten

def completed (cfg : Config) (m : Machine) : Bool :=
  (List.range cfg.lanes).all (fun t => (m.threads t).pc == .done)
 
def outputValues (cfg : Config) (m : Machine) : Array (Option UInt32) :=
  Array.ofFn (fun t : Fin cfg.n => m.output t)

/-- Every listed physical page must be fully allocated, including unused entries. -/
def ValidInput (cfg : Config) (input : Input) : Prop :=
  0 < cfg.pageSize ∧ cfg.n ≤ cfg.lanes ∧
  cfg.n ≤ input.pageTable.size * cfg.pageSize ∧
  ∀ p : Fin input.pageTable.size,
    physicalPage input p * cfg.pageSize + cfg.pageSize ≤ input.cache.size

instance (cfg : Config) (input : Input) : Decidable (ValidInput cfg input) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∀ _p : Fin input.pageTable.size, _))

def validateInput (cfg : Config) (input : Input) : Bool := decide (ValidInput cfg input)

@[simp] theorem validateInput_eq_true : validateInput cfg input = true ↔ ValidInput cfg input := by
  simp [validateInput]

end Keystone.GPU

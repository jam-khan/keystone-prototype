import Std

/-!
Structured source and flat target semantics for one GPU thread, using UInt64
arithmetic. The page table and KV cache are read-only and separate from output.
CUDA scheduling and weak memory are outside this model.
-/
namespace Keystone.Lowering

inductive Op where
  | add | mul | div | mod
  deriving Repr, DecidableEq

/-- Kernel arguments: this thread's ID, the request's token count, and the page size. -/
inductive Param where
  | tid | numTokens | pageSize
  deriving Repr, DecidableEq

inductive Expr where
  | lit (value : UInt64)
  | arg (parameter : Param)
  | local (id : Nat)
  | bin (op : Op) (lhs rhs : Expr)
  deriving Repr, DecidableEq

inductive Cmd where
  | skip
  | seq (first second : Cmd)
  | set (id : Nat) (value : Expr)
  | loadPageTable (id : Nat) (index : Expr)
  | loadKVCache (id : Nat) (index : Expr)
  | store (index value : Expr)
  | whenLt (lhs rhs : Expr) (body : Cmd)
  deriving Repr, DecidableEq

/-- Flat IR: no expression trees or structured commands. -/
inductive Instr where
  | lit (value : UInt64)
  | arg (parameter : Param)
  | local (id : Nat)
  | bin (op : Op)
  | set (id : Nat)
  | loadPageTable (id : Nat)
  | loadKVCache (id : Nat)
  | store
  | enterMask
  | leaveMask
  deriving Repr, DecidableEq

/-- What one thread can see: its arguments and the two read-only buffers. -/
structure Context where
  tid : UInt64
  numTokens : UInt64
  pageSize : UInt64
  pageTable : Array UInt64
  kvCache : Array UInt32
  deriving Repr, DecidableEq

inductive Buffer where
  | pageTable | kvCache | output
  deriving Repr, DecidableEq

structure Access where
  thread : UInt64
  buffer : Buffer
  index : UInt64
  deriving Repr, DecidableEq

structure State where
  locals : Nat → UInt64 := fun _ => 0
  output : Nat → UInt32 := fun _ => 0
  trace : List Access := []

inductive Fault where
  | outOfBounds (buffer : Buffer) (index : UInt64)
  | stackUnderflow
  | maskUnderflow
  deriving Repr, DecidableEq

/-- Faults retain all preceding writes and successful access events. -/
abbrev Result (α : Type) := Except (Fault × State) α

structure Target where
  state : State
  stack : List UInt64 := []
  active : Bool := true
  masks : List Bool := []

def getArg (ctx : Context) : Param → UInt64
  | .tid => ctx.tid
  | .numTokens => ctx.numTokens
  | .pageSize => ctx.pageSize

def applyOp : Op → UInt64 → UInt64 → UInt64
  | .add, a, b => a + b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b

def Expr.eval : Expr → Context → State → UInt64
  | .lit value, _, _ => value
  | .arg parameter, ctx, _ => getArg ctx parameter
  | .local id, _, state => state.locals id
  | .bin op lhs rhs, ctx, state => applyOp op (lhs.eval ctx state) (rhs.eval ctx state)

def setLocal (state : State) (id : Nat) (value : UInt64) : State :=
  { state with locals := fun j => if j = id then value else state.locals j }

def record (ctx : Context) (state : State) (buffer : Buffer) (index : UInt64) : State :=
  { state with trace := state.trace ++ [⟨ctx.tid, buffer, index⟩] }

/-- Memory primitives shared by the source and target interpreters. -/
def readPageTable (ctx : Context) (state : State) (index : UInt64) : Result (State × UInt64) :=
  if index.toNat < ctx.pageTable.size then
    .ok (record ctx state .pageTable index, ctx.pageTable[index.toNat]!)
  else .error (.outOfBounds .pageTable index, state)

def readKVCache (ctx : Context) (state : State) (index : UInt64) : Result (State × UInt64) :=
  if index.toNat < ctx.kvCache.size then
    .ok (record ctx state .kvCache index, ctx.kvCache[index.toNat]!.toUInt64)
  else .error (.outOfBounds .kvCache index, state)

def writeOutput (ctx : Context) (state : State) (index value : UInt64) : Result State :=
  if index < ctx.numTokens then
    .ok { record ctx state .output index with
      output := fun j => if j = index.toNat then value.toUInt32 else state.output j }
  else .error (.outOfBounds .output index, state)

/-- Structured source execution, in left-to-right order. -/
def source : Cmd → Context → State → Result State
  | .skip, _, state => .ok state
  | .seq first second, ctx, state =>
    (source first ctx state).bind (source second ctx)
  | .set id value, ctx, state => .ok (setLocal state id (value.eval ctx state))
  | .loadPageTable id index, ctx, state =>
    (readPageTable ctx state (index.eval ctx state)).map fun (next, value) => setLocal next id value
  | .loadKVCache id index, ctx, state =>
    (readKVCache ctx state (index.eval ctx state)).map fun (next, value) => setLocal next id value
  | .store index value, ctx, state =>
    writeOutput ctx state (index.eval ctx state) (value.eval ctx state)
  | .whenLt lhs rhs body, ctx, state =>
    if lhs.eval ctx state < rhs.eval ctx state then source body ctx state else .ok state

/-- Mask management always executes; other instructions run only when active. -/
def targetStep (instruction : Instr) (ctx : Context) (machine : Target) : Result Target :=
  match instruction with
  | .enterMask =>
    if machine.active then
      match machine.stack with
      | rhs :: lhs :: rest => .ok { machine with stack := rest, active := lhs < rhs, masks := machine.active :: machine.masks }
      | _ => .error (.stackUnderflow, machine.state)
    else .ok { machine with masks := false :: machine.masks }
  | .leaveMask =>
    match machine.masks with
    | previous :: rest => .ok { machine with active := previous, masks := rest }
    | [] => .error (.maskUnderflow, machine.state)
  | .lit value =>
    if machine.active then .ok { machine with stack := value :: machine.stack } else .ok machine
  | .arg parameter =>
    if machine.active then .ok { machine with stack := getArg ctx parameter :: machine.stack } else .ok machine
  | .local id =>
    if machine.active then .ok { machine with stack := machine.state.locals id :: machine.stack } else .ok machine
  | .bin op =>
    if !machine.active then .ok machine else
    match machine.stack with
    | rhs :: lhs :: rest => .ok { machine with stack := applyOp op lhs rhs :: rest }
    | _ => .error (.stackUnderflow, machine.state)
  | .set id =>
    if !machine.active then .ok machine else
    match machine.stack with
    | value :: rest => .ok { machine with state := setLocal machine.state id value, stack := rest }
    | _ => .error (.stackUnderflow, machine.state)
  | .loadPageTable id =>
    if !machine.active then .ok machine else
    match machine.stack with
    | index :: rest => (readPageTable ctx machine.state index).map fun (next, value) =>
        { machine with state := setLocal next id value, stack := rest }
    | _ => .error (.stackUnderflow, machine.state)
  | .loadKVCache id =>
    if !machine.active then .ok machine else
    match machine.stack with
    | index :: rest => (readKVCache ctx machine.state index).map fun (next, value) =>
        { machine with state := setLocal next id value, stack := rest }
    | _ => .error (.stackUnderflow, machine.state)
  | .store =>
    if !machine.active then .ok machine else
    match machine.stack with
    | value :: index :: rest => (writeOutput ctx machine.state index value).map fun next =>
        { machine with state := next, stack := rest }
    | _ => .error (.stackUnderflow, machine.state)

def target : List Instr → Context → Target → Result Target
  | [], _, machine => .ok machine
  | instruction :: rest, ctx, machine =>
    (targetStep instruction ctx machine).bind (target rest ctx)

end Keystone.Lowering

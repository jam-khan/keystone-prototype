import Std

/-!
Structured source and flat target semantics for one lane, using UInt64 arithmetic.
Inputs are immutable and separate from output. CUDA scheduling and weak memory
are outside this model.
-/
namespace Keystone.Lowering

inductive Op where
  | add | mul | div | mod
  deriving Repr, DecidableEq

inductive Param where
  | lane | tokens | pageSize
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
  | loadTable (id : Nat) (address : Expr)
  | loadCache (id : Nat) (address : Expr)
  | store (address value : Expr)
  | whenLt (lhs rhs : Expr) (body : Cmd)
  deriving Repr, DecidableEq

/-- Flat IR: no expression trees or structured commands. -/
inductive Instr where
  | lit (value : UInt64)
  | arg (parameter : Param)
  | local (id : Nat)
  | bin (op : Op)
  | set (id : Nat)
  | loadTable (id : Nat)
  | loadCache (id : Nat)
  | store
  | enterMask
  | leaveMask
  deriving Repr, DecidableEq

structure Context where
  lane : UInt64
  tokens : UInt64
  pageSize : UInt64
  table : Array UInt64
  cache : Array UInt32
  deriving Repr, DecidableEq

inductive Space where
  | table | cache | output
  deriving Repr, DecidableEq

structure Access where
  lane : UInt64
  space : Space
  address : UInt64
  deriving Repr, DecidableEq

structure State where
  locals : Nat → UInt64 := fun _ => 0
  output : Nat → UInt32 := fun _ => 0
  trace : List Access := []

inductive Fault where
  | outOfBounds (space : Space) (address : UInt64)
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
  | .lane => ctx.lane
  | .tokens => ctx.tokens
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

def record (ctx : Context) (state : State) (space : Space) (address : UInt64) : State :=
  { state with trace := state.trace ++ [⟨ctx.lane, space, address⟩] }

/-- Memory primitives shared by the source and target interpreters. -/
def readTable (ctx : Context) (state : State) (address : UInt64) : Result (State × UInt64) :=
  if address.toNat < ctx.table.size then
    .ok (record ctx state .table address, ctx.table[address.toNat]!)
  else .error (.outOfBounds .table address, state)

def readCache (ctx : Context) (state : State) (address : UInt64) : Result (State × UInt64) :=
  if address.toNat < ctx.cache.size then
    .ok (record ctx state .cache address, ctx.cache[address.toNat]!.toUInt64)
  else .error (.outOfBounds .cache address, state)

def writeOutput (ctx : Context) (state : State) (address value : UInt64) : Result State :=
  if address < ctx.tokens then
    .ok { record ctx state .output address with
      output := fun j => if j = address.toNat then value.toUInt32 else state.output j }
  else .error (.outOfBounds .output address, state)

/-- Structured source execution, in left-to-right order. -/
def source : Cmd → Context → State → Result State
  | .skip, _, state => .ok state
  | .seq first second, ctx, state =>
    (source first ctx state).bind (source second ctx)
  | .set id value, ctx, state => .ok (setLocal state id (value.eval ctx state))
  | .loadTable id address, ctx, state =>
    (readTable ctx state (address.eval ctx state)).map fun (next, value) => setLocal next id value
  | .loadCache id address, ctx, state =>
    (readCache ctx state (address.eval ctx state)).map fun (next, value) => setLocal next id value
  | .store address value, ctx, state =>
    writeOutput ctx state (address.eval ctx state) (value.eval ctx state)
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
  | .loadTable id =>
    if !machine.active then .ok machine else
    match machine.stack with
    | address :: rest => (readTable ctx machine.state address).map fun (next, value) =>
        { machine with state := setLocal next id value, stack := rest }
    | _ => .error (.stackUnderflow, machine.state)
  | .loadCache id =>
    if !machine.active then .ok machine else
    match machine.stack with
    | address :: rest => (readCache ctx machine.state address).map fun (next, value) =>
        { machine with state := setLocal next id value, stack := rest }
    | _ => .error (.stackUnderflow, machine.state)
  | .store =>
    if !machine.active then .ok machine else
    match machine.stack with
    | value :: address :: rest => (writeOutput ctx machine.state address value).map fun next =>
        { machine with state := next, stack := rest }
    | _ => .error (.stackUnderflow, machine.state)

def target : List Instr → Context → Target → Result Target
  | [], _, machine => .ok machine
  | instruction :: rest, ctx, machine =>
    (targetStep instruction ctx machine).bind (target rest ctx)

end Keystone.Lowering

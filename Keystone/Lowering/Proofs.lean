import Keystone.Lowering.Compiler

namespace Keystone.Lowering

theorem target_append (first second : List Instr) (ctx : Context) (machine : Target) :
    target (first ++ second) ctx machine =
      (target first ctx machine).bind (target second ctx) := by
  induction first generalizing machine with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [List.cons_append, target]
    cases targetStep instruction ctx machine <;> simp_all [Except.bind]

/-- Expression code pushes one result and preserves the surrounding state. -/
theorem compileExpr_correct (expression : Expr) (ctx : Context) (state : State)
    (stack : List UInt64) (masks : List Bool) :
    target (compileExpr expression) ctx ⟨state, stack, true, masks⟩ =
      .ok ⟨state, expression.eval ctx state :: stack, true, masks⟩ := by
  induction expression generalizing stack with
  | lit value => rfl
  | arg parameter => rfl
  | «local» id => rfl
  | bin op lhs rhs ihl ihr =>
    simp only [compileExpr, target_append, ihl]
    change (target (compileExpr rhs) ctx ⟨state, lhs.eval ctx state :: stack, true, masks⟩).bind _ = _
    rw [ihr]
    rfl

/-- Inactive expression code leaves the entire machine unchanged. -/
theorem compileExpr_inactive (expression : Expr) (ctx : Context) (state : State)
    (stack : List UInt64) (masks : List Bool) :
    target (compileExpr expression) ctx ⟨state, stack, false, masks⟩ =
      .ok ⟨state, stack, false, masks⟩ := by
  induction expression with
  | lit value => rfl
  | arg parameter => rfl
  | «local» id => rfl
  | bin op lhs rhs ihl ihr =>
    simp only [compileExpr, target_append, ihl]
    change (target (compileExpr rhs) ctx ⟨state, stack, false, masks⟩).bind _ = _
    rw [ihr]
    rfl

/-- Inactive commands are silent and restore the caller’s mask frame. -/
theorem compile_inactive (command : Cmd) (ctx : Context) (state : State)
    (stack : List UInt64) (masks : List Bool) :
    target (compile command) ctx ⟨state, stack, false, masks⟩ =
      .ok ⟨state, stack, false, masks⟩ := by
  induction command generalizing masks with
  | skip => rfl
  | seq first second ihf ihs =>
    simp [compile, target_append, ihf, ihs, Except.bind]
  | set id value =>
    simp [compile, target_append, compileExpr_inactive, Except.bind, target, targetStep]
  | loadTable id address =>
    simp [compile, target_append, compileExpr_inactive, Except.bind, target, targetStep]
  | loadCache id address =>
    simp [compile, target_append, compileExpr_inactive, Except.bind, target, targetStep]
  | store address value =>
    simp [compile, target_append, compileExpr_inactive, Except.bind, target, targetStep]
  | whenLt lhs rhs body ih =>
    simp [compile, target_append, compileExpr_inactive, Except.bind, target, targetStep, ih]

/-- Preserve state, trace, and faults for arbitrary inputs; restore caller frames
on success. No valid-memory premise is needed. -/
theorem compile_correct (command : Cmd) (ctx : Context) (state : State)
    (stack : List UInt64) (masks : List Bool) :
    target (compile command) ctx ⟨state, stack, true, masks⟩ =
      (source command ctx state).map (fun next => ⟨next, stack, true, masks⟩) := by
  induction command generalizing state stack masks with
  | skip => rfl
  | seq first second ihf ihs =>
    simp only [compile, target_append, ihf, source]
    cases hf : source first ctx state <;> simp [Except.bind, Except.map, ihs]
  | set id value =>
    simp [compile, target_append, compileExpr_correct, Except.bind, target, targetStep, source, Except.map]
  | loadTable id address =>
    simp only [compile, target_append, compileExpr_correct, Except.bind]
    cases hr : readTable ctx state (address.eval ctx state) <;>
      simp_all [Except.bind, target, targetStep, source, Except.map]
  | loadCache id address =>
    simp only [compile, target_append, compileExpr_correct, Except.bind]
    cases hr : readCache ctx state (address.eval ctx state) <;>
      simp_all [Except.bind, target, targetStep, source, Except.map]
  | store address value =>
    simp only [compile, target_append, compileExpr_correct, Except.bind]
    cases hr : writeOutput ctx state (address.eval ctx state) (value.eval ctx state) <;>
      simp_all [Except.bind, target, targetStep, source, Except.map]
  | whenLt lhs rhs body ih =>
    simp only [compile, target_append, compileExpr_correct, Except.bind]
    by_cases h : lhs.eval ctx state < rhs.eval ctx state
    · simp [Except.bind, target, targetStep, h, ih, source]
      cases source body ctx state <;> rfl
    · simp [Except.bind, target, targetStep, h, compile_inactive, source, Except.map]

/-- Successful execution preserves state and trace. -/
theorem compile_success (hs : source command ctx state = .ok next)
    (stack : List UInt64) (masks : List Bool) :
    target (compile command) ctx ⟨state, stack, true, masks⟩ =
      .ok ⟨next, stack, true, masks⟩ := by
  rw [compile_correct, hs]
  rfl

/-- Failure preserves the fault and all preceding state changes and events. -/
theorem compile_failure (hs : source command ctx state = .error (fault, partialState))
    (stack : List UInt64) (masks : List Bool) :
    target (compile command) ctx ⟨state, stack, true, masks⟩ =
      .error (fault, partialState) := by
  rw [compile_correct, hs]
  rfl

/-- Source commands can fail only through a checked memory operation. -/
def MemoryFault : Fault → Prop
  | .outOfBounds _ _ => True
  | .stackUnderflow | .maskUnderflow => False

theorem source_fault_is_memory
    (failure : source command ctx state = .error (fault, partialState)) : MemoryFault fault := by
  induction command generalizing state with
  | skip => cases failure
  | set id value => cases failure
  | seq first second ihf ihs =>
    simp only [source] at failure
    cases hs : source first ctx state with
    | error pair =>
      rw [hs] at failure
      cases failure
      exact ihf hs
    | ok next =>
      rw [hs] at failure
      exact ihs failure
  | loadTable id address =>
    simp only [source, readTable] at failure
    split at failure <;> simp only [Except.map] at failure
    · cases failure
    · cases failure
      trivial
  | loadCache id address =>
    simp only [source, readCache] at failure
    split at failure <;> simp only [Except.map] at failure
    · cases failure
    · cases failure
      trivial
  | store address value =>
    simp only [source, writeOutput] at failure
    split at failure
    · cases failure
    · cases failure
      trivial
  | whenLt lhs rhs body ih =>
    simp only [source] at failure
    split at failure
    · exact ih failure
    · cases failure

/-- Compiled programs cannot introduce operand-stack or mask-stack underflow. -/
theorem compiled_fault_is_memory
    (failure : target (compile command) ctx ⟨state, stack, true, masks⟩ =
      .error (fault, partialState)) : MemoryFault fault := by
  rw [compile_correct] at failure
  cases hs : source command ctx state with
  | error pair =>
    rw [hs] at failure
    cases failure
    exact source_fault_is_memory hs
  | ok next =>
    rw [hs] at failure
    cases failure

end Keystone.Lowering

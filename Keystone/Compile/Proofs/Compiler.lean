import Keystone.GPU.KVGather -- Source instructions and their execution.
import Keystone.Compile.Target -- Target block interpreter and register operations.
import Keystone.Compile.Compiler -- Instruction selection and token calculation.

namespace Keystone.Compile

/-- Execute a selected block and discard its scratch register: the source step remains. -/
theorem execute_compiled_block
    (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat) (s : GPU.KernelState)
    (ht : tid < cfg.numThreads) :
    (do
      let (frame, accesses) ← executeBlock cfg mem tid (compile (s.threads tid).instr) ⟨s, 0⟩
      pure (frame.kernel, accesses)) =
    (GPU.step cfg mem tid s).map (fun (next, access) => (next, access.toList)) := by
  simp only [GPU.step, ite_eq_right (Nat.not_le.mpr ht)]
  by_cases htable : (s.threads tid).logicalPage ≥ mem.pageTable.size <;>
    by_cases hcache : (s.threads tid).kvIndex ≥ mem.kvCache.size <;>
    by_cases houtput : tid + (s.threads tid).round * cfg.numThreads ≥ cfg.numTokens <;>
    cases hp : (s.threads tid).instr <;>
    simp +contextual [htable, hcache, houtput, hp, compile, computeToken, executeBlock,
      executeInstruction, operandValue, readRegister, writeRegister,
      arithmeticValue, jump, GPU.token, GPU.physicalPage,
      GPU.withThread, GPU.withOutput, Bind.bind, Pure.pure,
      Except.bind, Except.map, Except.pure] <;> rfl

end Keystone.Compile

import Keystone.Compile.Compiler

namespace Keystone.Compile

private def stageNumber : GPU.Instr → Nat
  | .guard => 0 | .page => 1 | .table => 2 | .kvIndex => 3
  | .load => 4 | .store => 5 | .done => 6

private def registerC : Register → String
  | .round => "t->round" | .logicalPage => "t->logical_page"
  | .physicalPage => "t->physical_page" | .kvIndex => "t->kv_index" | .temp => "temp"

private def operandC : Operand → String
  | .constant value => s!"UINT64_C({value})"
  | .threadId => "tid" | .numTokens => "cfg.num_tokens"
  | .pageSize => "cfg.page_size" | .numThreads => "cfg.num_threads"
  | .register reg => registerC reg

private def accessC (buffer : Nat) (index bound action : String) : String :=
  s!"index = {index};\n" ++
  "*access = (KgAccess){tid, " ++ s!"{buffer}, index" ++ "};\n" ++
  s!"if (index >= {bound}) " ++ "{ fault->access = *access; return KG_OUT_OF_BOUNDS; }\n" ++
  s!"{action}\n*has_access = 1;\n"

private def instructionC : Instruction → String
  | .binary op dest lhs rhs =>
      let operation := match op with
        | .add => "if (b > UINT64_MAX - a) return KG_OVERFLOW;\n" ++
            s!"{registerC dest} = a + b;\n"
        | .mul => "if (b != 0 && a > UINT64_MAX / b) return KG_OVERFLOW;\n" ++
            s!"{registerC dest} = a * b;\n"
        | .div => s!"{registerC dest} = b == 0 ? 0 : a / b;\n"
        | .mod => s!"{registerC dest} = b == 0 ? a : a % b;\n"
      s!"a = {operandC lhs}; b = {operandC rhs};\n" ++ operation
  | .readPageTable dest index =>
      accessC 0 (operandC index) "mem.page_table_size"
        s!"{registerC dest} = mem.page_table[index];"
  | .readKVCache index =>
      accessC 1 (operandC index) "mem.kv_cache_size" "t->entry = mem.kv_cache[index];"
  | .storeOutput index =>
      accessC 2 (operandC index) "cfg.num_tokens"
        "state->output[index] = t->entry; state->present[index] = 1;"
  | .jump next => s!"t->pc = {stageNumber next};\n"
  | .branchLt lhs rhs yes no =>
      s!"t->pc = {operandC lhs} < {operandC rhs} ? {stageNumber yes} : {stageNumber no};\n"

private def blockC (stage : GPU.Instr) : String :=
  s!"case {stageNumber stage}:\n" ++
    String.join ((compile stage).map instructionC) ++ "return KG_OK;\n"

/-- Trusted C99 serialization of `compile`; there is no C correctness theorem.
    Indices use checked uint64 arithmetic. Buffers must have their declared lengths,
    inputs stay immutable, writable buffers are disjoint, and states start at zero.
    After any error, only the status/fault is observable; discard state and trace. -/
def emitC : String := r#"
/* Trusted C99 emission: no theorem covers C or machine integers.
 * CPU replay: one scheduled turn executes one entire compiled block.
 * Zero-initialize threads[num_threads], output[num_tokens], present[num_tokens].
 * Inputs have their declared lengths and remain immutable.
 * Writable buffers are mutually disjoint and do not alias inputs.
 * trace[count] suffices: each current block makes at most one memory access.
 * On error, discard state/trace; only OUT_OF_BOUNDS uses fault.access,
 * and only INVALID_THREAD uses fault.thread. Overflow never silently wraps.
 */
#include <stdint.h>
#include <stddef.h>

typedef struct { uint64_t num_tokens, page_size, num_threads; } KgConfig;
typedef struct {
  const uint64_t *page_table;
  uint64_t page_table_size;
  const uint32_t *kv_cache;
  uint64_t kv_cache_size;
} KgMemory;
typedef struct {
  unsigned pc;
  uint64_t round, logical_page, physical_page, kv_index;
  uint32_t entry;
} KgThread;
typedef struct { KgThread *threads; uint32_t *output; unsigned char *present; } KgState;
/* buffer: 0 = page table, 1 = KV cache, 2 = output. */
typedef struct { uint64_t thread; unsigned buffer; uint64_t index; } KgAccess;
typedef struct { uint64_t thread; KgAccess access; } KgFault;
typedef enum {
  KG_OK, KG_INVALID_THREAD, KG_OUT_OF_BOUNDS, KG_OVERFLOW,
  KG_TRACE_FULL, KG_INVALID_PC
} KgStatus;

KgStatus kg_step(KgConfig cfg, KgMemory mem, uint64_t tid, KgState *state,
                 KgAccess *access, int *has_access, KgFault *fault) {
  *has_access = 0;
  if (tid >= cfg.num_threads) { fault->thread = tid; return KG_INVALID_THREAD; }
  KgThread *t = &state->threads[tid];
  uint64_t temp = 0, a, b, index;
  switch (t->pc) {
"# ++ String.join ([GPU.Instr.guard, .page, .table, .kvIndex, .load, .store, .done].map blockC) ++ r#"default: return KG_INVALID_PC;
  }
}

KgStatus kg_run(KgConfig cfg, KgMemory mem, KgState *state,
                const uint64_t *schedule, size_t count,
                KgAccess *trace, size_t capacity, size_t *trace_length, KgFault *fault) {
  *trace_length = 0;
  for (size_t i = 0; i < count; ++i) {
    KgAccess access;
    int has_access;
    KgStatus status = kg_step(cfg, mem, schedule[i], state, &access, &has_access, fault);
    if (status != KG_OK) return status;
    if (has_access) {
      if (*trace_length == capacity) return KG_TRACE_FULL;
      trace[(*trace_length)++] = access;
    }
  }
  return KG_OK;
}
"#

end Keystone.Compile

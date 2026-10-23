
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
case 0:
a = t->round; b = cfg.num_threads;
if (b != 0 && a > UINT64_MAX / b) return KG_OVERFLOW;
temp = a * b;
a = tid; b = temp;
if (b > UINT64_MAX - a) return KG_OVERFLOW;
temp = a + b;
t->pc = temp < cfg.num_tokens ? 1 : 6;
return KG_OK;
case 1:
a = t->round; b = cfg.num_threads;
if (b != 0 && a > UINT64_MAX / b) return KG_OVERFLOW;
temp = a * b;
a = tid; b = temp;
if (b > UINT64_MAX - a) return KG_OVERFLOW;
temp = a + b;
a = temp; b = cfg.page_size;
t->logical_page = b == 0 ? 0 : a / b;
t->pc = 2;
return KG_OK;
case 2:
index = t->logical_page;
*access = (KgAccess){tid, 0, index};
if (index >= mem.page_table_size) { fault->access = *access; return KG_OUT_OF_BOUNDS; }
t->physical_page = mem.page_table[index];
*has_access = 1;
t->pc = 3;
return KG_OK;
case 3:
a = t->round; b = cfg.num_threads;
if (b != 0 && a > UINT64_MAX / b) return KG_OVERFLOW;
temp = a * b;
a = tid; b = temp;
if (b > UINT64_MAX - a) return KG_OVERFLOW;
temp = a + b;
a = temp; b = cfg.page_size;
temp = b == 0 ? a : a % b;
a = t->physical_page; b = cfg.page_size;
if (b != 0 && a > UINT64_MAX / b) return KG_OVERFLOW;
t->kv_index = a * b;
a = t->kv_index; b = temp;
if (b > UINT64_MAX - a) return KG_OVERFLOW;
t->kv_index = a + b;
t->pc = 4;
return KG_OK;
case 4:
index = t->kv_index;
*access = (KgAccess){tid, 1, index};
if (index >= mem.kv_cache_size) { fault->access = *access; return KG_OUT_OF_BOUNDS; }
t->entry = mem.kv_cache[index];
*has_access = 1;
t->pc = 5;
return KG_OK;
case 5:
a = t->round; b = cfg.num_threads;
if (b != 0 && a > UINT64_MAX / b) return KG_OVERFLOW;
temp = a * b;
a = tid; b = temp;
if (b > UINT64_MAX - a) return KG_OVERFLOW;
temp = a + b;
index = temp;
*access = (KgAccess){tid, 2, index};
if (index >= cfg.num_tokens) { fault->access = *access; return KG_OUT_OF_BOUNDS; }
state->output[index] = t->entry; state->present[index] = 1;
*has_access = 1;
a = t->round; b = UINT64_C(1);
if (b > UINT64_MAX - a) return KG_OVERFLOW;
t->round = a + b;
t->pc = 0;
return KG_OK;
case 6:
return KG_OK;
default: return KG_INVALID_PC;
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

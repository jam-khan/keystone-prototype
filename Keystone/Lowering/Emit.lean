import Keystone.Lowering.Language
import Lean.Data.Json

/-!
Trusted serialization of the *compiled flat target*, not another source compiler.
The refinement theorem stops before this emitter and the system C/CUDA compiler.
Every instruction is emitted, including inactive predicate and total division rules.
Native checks fail before invalid memory accesses. These checks are not GPU proofs.
-/
namespace Keystone.Lowering
open Lean

private def opName : Op → String
  | .add => "add" | .mul => "mul" | .div => "div" | .mod => "mod"

private def paramName : Param → String
  | .tid => "tid" | .numTokens => "num_tokens" | .pageSize => "page_size"

def instrJson : Instr → Json
  | .lit value => Json.mkObj [("op", toJson "lit"), ("value", toJson value.toNat)]
  | .arg parameter => Json.mkObj [("op", toJson "arg"), ("parameter", toJson (paramName parameter))]
  | .bin op => Json.mkObj [("op", toJson "bin"), ("operator", toJson (opName op))]
  | .local id => Json.mkObj [("op", toJson "local"), ("id", toJson id)]
  | .set id => Json.mkObj [("op", toJson "set"), ("id", toJson id)]
  | .loadPageTable id => Json.mkObj [("op", toJson "load_page_table"), ("id", toJson id)]
  | .loadKVCache id => Json.mkObj [("op", toJson "load_kv_cache"), ("id", toJson id)]
  | .store => Json.mkObj [("op", toJson "store")]
  | .enterMask => Json.mkObj [("op", toJson "enter_mask")]
  | .leaveMask => Json.mkObj [("op", toJson "leave_mask")]

def programJson (code : List Instr) : Json := toJson (code.map instrJson)

def emitListing (code : List Instr) : String :=
  String.intercalate "\n" (code.zipIdx |>.map fun (instruction, index) =>
    s!"{index}: {(instrJson instruction).compress}")

/-- Dense slots avoid allocating an enormous array for a sparse source local ID. -/
private def locals (code : List Instr) : List Nat :=
  code.foldl (fun ids instruction =>
    match instruction with
    | .local id | .set id | .loadPageTable id | .loadKVCache id =>
        if id ∈ ids then ids else ids ++ [id]
    | _ => ids) []

private def slot (ids : List Nat) (id : Nat) : String := s!"locals[{ids.idxOf id}]"

private def guarded (body : String) : String :=
  "  if (active) {\n" ++ body ++ "  }\n"

private def push (value : String) : String := guarded s!"    stack[sp++] = {value};\n"

private def emitInstruction (ids : List Nat) : Instr → String
  | .lit value => push s!"UINT64_C({value.toNat})"
  | .arg parameter => push (paramName parameter)
  | .local id => push (slot ids id)
  | .bin op => guarded (
      "    if (sp < 2) return 4;\n" ++
      "    const uint64_t rhs = stack[--sp];\n    const uint64_t lhs = stack[--sp];\n" ++
      "    stack[sp++] = " ++ (match op with
        | .add => "lhs + rhs" | .mul => "lhs * rhs"
        | .div => "rhs == 0 ? UINT64_C(0) : lhs / rhs"
        | .mod => "rhs == 0 ? lhs : lhs % rhs") ++ ";\n")
  | .set id => guarded ("    if (sp < 1) return 4;\n" ++
      s!"    {slot ids id} = stack[--sp];\n")
  | .loadPageTable id => guarded ("    if (sp < 1) return 4;\n" ++
      "    const uint64_t index = stack[--sp];\n" ++
      "    if (index >= page_table_length) return 1;\n" ++
      s!"    {slot ids id} = page_table[index];\n")
  | .loadKVCache id => guarded ("    if (sp < 1) return 4;\n" ++
      "    const uint64_t index = stack[--sp];\n" ++
      "    if (index >= kv_cache_length) return 2;\n" ++
      s!"    {slot ids id} = (uint64_t)kv_cache[index];\n")
  | .store => guarded (
      "    if (sp < 2) return 4;\n" ++
      "    const uint64_t value = stack[--sp];\n    const uint64_t index = stack[--sp];\n" ++
      "    if (index >= num_tokens || index >= out_length) return 3;\n" ++
      "    out[index] = (uint32_t)value;\n")
  | .enterMask =>
      "  if (active) {\n" ++
      "    if (sp < 2) return 4;\n" ++
      "    const uint64_t rhs = stack[--sp];\n    const uint64_t lhs = stack[--sp];\n" ++
      "    masks[mp++] = active;\n    active = lhs < rhs;\n" ++
      "  } else { masks[mp++] = 0; }\n"
  | .leaveMask => "  if (mp < 1) return 5;\n  active = masks[--mp];\n"

private def arguments : String :=
  "const uint32_t *kv_cache, uint64_t kv_cache_length, " ++
  "const uint64_t *page_table, uint64_t page_table_length, " ++
  "uint32_t *out, uint64_t out_length, uint64_t page_size, uint64_t num_tokens, uint64_t tid"

private def threadBody (code : List Instr) (cuda : Bool) : String := Id.run do
  let ids := locals code
  let qualifier := if cuda then "static __device__" else "static"
  return qualifier ++ " int lowered_thread(" ++ arguments ++ ") {\n" ++
    s!"  uint64_t stack[{code.length + 1}] = " ++ "{0};\n" ++
    s!"  uint64_t locals[{ids.length + 1}] = " ++ "{0};\n" ++
    s!"  unsigned char masks[{code.length + 1}] = " ++ "{0};\n" ++
    "  uint64_t sp = 0, mp = 0;\n  unsigned char active = 1;\n" ++
    String.join (code.map (emitInstruction ids)) ++ "  return 0;\n}\n"

private def cpuWrapper : String := "
/* Status: 1 page-table bounds, 2 KV-cache bounds, 3 output bounds,
           4 value-stack underflow, 5 predicate-stack underflow. */
int lowered_kernel(const uint32_t *kv_cache, uint64_t kv_cache_length,
    const uint64_t *page_table, uint64_t page_table_length, uint32_t *out,
    uint64_t out_length, uint64_t page_size, uint64_t num_tokens, uint64_t num_threads) {
  for (uint64_t tid = 0; tid < num_threads; ++tid) {
    const int status = lowered_thread(kv_cache, kv_cache_length, page_table, page_table_length,
        out, out_length, page_size, num_tokens, tid);
    if (status != 0) return status;
  }
  return 0;
}
"

def emitC (code : List Instr) : String :=
  "/* Generated from flat target instructions by Lean. Emitter/compiler trusted. */\n" ++
  "#include <stdint.h>\n" ++ threadBody code false ++ cpuWrapper

private def cudaWrapper : String := "
__global__ void lowered_device(const uint32_t *kv_cache, uint64_t kv_cache_length,
    const uint64_t *page_table, uint64_t page_table_length, uint32_t *out,
    uint64_t out_length, uint64_t page_size, uint64_t num_tokens,
    uint64_t num_threads, int *statuses) {
  const uint64_t tid = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
  if (tid < num_threads) statuses[tid] = lowered_thread(kv_cache, kv_cache_length,
      page_table, page_table_length, out, out_length, page_size, num_tokens, tid);
}
extern \"C\" int available_devices(int *count) {
  return (int)cudaGetDeviceCount(count);
}
extern \"C\" const char *cuda_error(int code) {
  return cudaGetErrorString((cudaError_t)code);
}
/* CUDA errors are 1000 + cudaError_t; semantic faults retain codes 1..5.
   Only launch programs whose inter-thread output accesses are race-free.
   Each thread has a separate status slot; faults never perform invalid accesses.
   Other threads continue after a fault, unlike the sequential CPU launcher.
   Cross-backend equality is claimed only for successful race-free launches. */
extern \"C\" int lowered_kernel(const uint32_t *kv_cache, uint64_t kv_cache_length,
    const uint64_t *page_table, uint64_t page_table_length, uint32_t *out,
    uint64_t out_length, uint64_t page_size, uint64_t num_tokens, uint64_t num_threads) {
  if (!num_threads) return 0;
  if (kv_cache_length > SIZE_MAX / sizeof(uint32_t) ||
      page_table_length > SIZE_MAX / sizeof(uint64_t) ||
      out_length > SIZE_MAX / sizeof(uint32_t) || num_threads > SIZE_MAX / sizeof(int))
    return 1000 + (int)cudaErrorInvalidValue;
  uint32_t *device_kv_cache = nullptr, *device_out = nullptr;
  uint64_t *device_page_table = nullptr;
  int *device_statuses = nullptr, *host_statuses = nullptr;
  int device, result = 0;
  cudaDeviceProp properties;
  cudaError_t status = cudaGetDevice(&device);
  if (status != cudaSuccess) return 1000 + (int)status;
  status = cudaGetDeviceProperties(&properties, device);
  if (status != cudaSuccess) return 1000 + (int)status;
  const int limit = properties.maxThreadsPerBlock < properties.maxThreadsDim[0] ?
      properties.maxThreadsPerBlock : properties.maxThreadsDim[0];
  const unsigned block = limit < 256 ? (unsigned)limit : 256;
  if (!block) return 1000 + (int)cudaErrorInvalidConfiguration;
  const uint64_t grid = num_threads / block + (num_threads % block != 0);
  if (grid > (uint64_t)properties.maxGridSize[0])
    return 1000 + (int)cudaErrorInvalidConfiguration;
  host_statuses = (int *)malloc(num_threads * sizeof(int));
  if (!host_statuses) return 1000 + (int)cudaErrorMemoryAllocation;
#define CUDA_TRY(call) do { status = (call); if (status != cudaSuccess) goto done; } while (0)
  if (kv_cache_length) {
    CUDA_TRY(cudaMalloc((void **)&device_kv_cache, kv_cache_length * sizeof(uint32_t)));
    CUDA_TRY(cudaMemcpy(device_kv_cache, kv_cache, kv_cache_length * sizeof(uint32_t), cudaMemcpyHostToDevice));
  }
  if (page_table_length) {
    CUDA_TRY(cudaMalloc((void **)&device_page_table, page_table_length * sizeof(uint64_t)));
    CUDA_TRY(cudaMemcpy(device_page_table, page_table, page_table_length * sizeof(uint64_t), cudaMemcpyHostToDevice));
  }
  if (out_length) {
    CUDA_TRY(cudaMalloc((void **)&device_out, out_length * sizeof(uint32_t)));
    CUDA_TRY(cudaMemcpy(device_out, out, out_length * sizeof(uint32_t), cudaMemcpyHostToDevice));
  }
  CUDA_TRY(cudaMalloc((void **)&device_statuses, num_threads * sizeof(int)));
  lowered_device<<<(unsigned)grid, block>>>(device_kv_cache, kv_cache_length, device_page_table,
      page_table_length, device_out, out_length, page_size, num_tokens, num_threads, device_statuses);
  CUDA_TRY(cudaGetLastError());
  CUDA_TRY(cudaDeviceSynchronize());
  CUDA_TRY(cudaMemcpy(host_statuses, device_statuses, num_threads * sizeof(int), cudaMemcpyDeviceToHost));
  if (out_length)
    CUDA_TRY(cudaMemcpy(out, device_out, out_length * sizeof(uint32_t), cudaMemcpyDeviceToHost));
  for (uint64_t tid = 0; tid < num_threads; ++tid)
    if (host_statuses[tid]) { result = host_statuses[tid]; break; }
done:
  void *buffers[4] = { device_statuses, device_out, device_page_table, device_kv_cache };
  for (void *buffer : buffers) {
    if (buffer) {
      cudaError_t cleanup = cudaFree(buffer);
      if (status == cudaSuccess) status = cleanup;
    }
  }
  free(host_statuses);
  return status == cudaSuccess ? result : 1000 + (int)status;
#undef CUDA_TRY
}
"

def emitCuda (code : List Instr) : String :=
  "/* Generated from flat target instructions by Lean. Emitter/compiler trusted. */\n" ++
  "#include <stdint.h>\n#include <stdlib.h>\n#include <cuda_runtime.h>\n" ++
  threadBody code true ++ cudaWrapper

end Keystone.Lowering

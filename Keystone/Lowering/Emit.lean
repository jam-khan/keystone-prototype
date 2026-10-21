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
  | .lane => "lane" | .tokens => "tokens" | .pageSize => "page_size"

def instrJson : Instr → Json
  | .lit value => Json.mkObj [("op", toJson "lit"), ("value", toJson value.toNat)]
  | .arg parameter => Json.mkObj [("op", toJson "arg"), ("parameter", toJson (paramName parameter))]
  | .bin op => Json.mkObj [("op", toJson "bin"), ("operator", toJson (opName op))]
  | .local id => Json.mkObj [("op", toJson "local"), ("id", toJson id)]
  | .set id => Json.mkObj [("op", toJson "set"), ("id", toJson id)]
  | .loadTable id => Json.mkObj [("op", toJson "load_table"), ("id", toJson id)]
  | .loadCache id => Json.mkObj [("op", toJson "load_cache"), ("id", toJson id)]
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
    | .local id | .set id | .loadTable id | .loadCache id =>
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
  | .loadTable id => guarded ("    if (sp < 1) return 4;\n" ++
      "    const uint64_t address = stack[--sp];\n" ++
      "    if (address >= table_length) return 1;\n" ++
      s!"    {slot ids id} = table[address];\n")
  | .loadCache id => guarded ("    if (sp < 1) return 4;\n" ++
      "    const uint64_t address = stack[--sp];\n" ++
      "    if (address >= cache_length) return 2;\n" ++
      s!"    {slot ids id} = (uint64_t)cache[address];\n")
  | .store => guarded (
      "    if (sp < 2) return 4;\n" ++
      "    const uint64_t value = stack[--sp];\n    const uint64_t address = stack[--sp];\n" ++
      "    if (address >= tokens || address >= out_length) return 3;\n" ++
      "    out[address] = (uint32_t)value;\n")
  | .enterMask =>
      "  if (active) {\n" ++
      "    if (sp < 2) return 4;\n" ++
      "    const uint64_t rhs = stack[--sp];\n    const uint64_t lhs = stack[--sp];\n" ++
      "    masks[mp++] = active;\n    active = lhs < rhs;\n" ++
      "  } else { masks[mp++] = 0; }\n"
  | .leaveMask => "  if (mp < 1) return 5;\n  active = masks[--mp];\n"

private def arguments : String :=
  "const uint32_t *cache, uint64_t cache_length, " ++
  "const uint64_t *table, uint64_t table_length, " ++
  "uint32_t *out, uint64_t out_length, uint64_t page_size, uint64_t tokens, uint64_t lane"

private def laneBody (code : List Instr) (cuda : Bool) : String := Id.run do
  let ids := locals code
  let qualifier := if cuda then "static __device__" else "static"
  return qualifier ++ " int lowered_lane(" ++ arguments ++ ") {\n" ++
    s!"  uint64_t stack[{code.length + 1}] = " ++ "{0};\n" ++
    s!"  uint64_t locals[{ids.length + 1}] = " ++ "{0};\n" ++
    s!"  unsigned char masks[{code.length + 1}] = " ++ "{0};\n" ++
    "  uint64_t sp = 0, mp = 0;\n  unsigned char active = 1;\n" ++
    String.join (code.map (emitInstruction ids)) ++ "  return 0;\n}\n"

private def cpuWrapper : String := "
/* Status: 1 table bounds, 2 cache bounds, 3 output bounds,
           4 value-stack underflow, 5 predicate-stack underflow. */
int lowered_kernel(const uint32_t *cache, uint64_t cache_length,
    const uint64_t *table, uint64_t table_length, uint32_t *out,
    uint64_t out_length, uint64_t page_size, uint64_t tokens, uint64_t lanes) {
  for (uint64_t lane = 0; lane < lanes; ++lane) {
    const int status = lowered_lane(cache, cache_length, table, table_length,
        out, out_length, page_size, tokens, lane);
    if (status != 0) return status;
  }
  return 0;
}
"

def emitC (code : List Instr) : String :=
  "/* Generated from flat target instructions by Lean. Emitter/compiler trusted. */\n" ++
  "#include <stdint.h>\n" ++ laneBody code false ++ cpuWrapper

private def cudaWrapper : String := "
__global__ void lowered_device(const uint32_t *cache, uint64_t cache_length,
    const uint64_t *table, uint64_t table_length, uint32_t *out,
    uint64_t out_length, uint64_t page_size, uint64_t tokens,
    uint64_t lanes, int *statuses) {
  const uint64_t lane = (uint64_t)blockIdx.x * blockDim.x + threadIdx.x;
  if (lane < lanes) statuses[lane] = lowered_lane(cache, cache_length,
      table, table_length, out, out_length, page_size, tokens, lane);
}
extern \"C\" int available_devices(int *count) {
  return (int)cudaGetDeviceCount(count);
}
extern \"C\" const char *cuda_error(int code) {
  return cudaGetErrorString((cudaError_t)code);
}
/* CUDA errors are 1000 + cudaError_t; semantic faults retain codes 1..5.
   Only launch programs whose inter-lane output accesses are race-free.
   Each lane has a separate status slot; faults never perform invalid accesses.
   Other lanes continue after a fault, unlike the sequential CPU launcher.
   Cross-backend equality is claimed only for successful race-free launches. */
extern \"C\" int lowered_kernel(const uint32_t *cache, uint64_t cache_length,
    const uint64_t *table, uint64_t table_length, uint32_t *out,
    uint64_t out_length, uint64_t page_size, uint64_t tokens, uint64_t lanes) {
  if (!lanes) return 0;
  if (cache_length > SIZE_MAX / sizeof(uint32_t) ||
      table_length > SIZE_MAX / sizeof(uint64_t) ||
      out_length > SIZE_MAX / sizeof(uint32_t) || lanes > SIZE_MAX / sizeof(int))
    return 1000 + (int)cudaErrorInvalidValue;
  uint32_t *device_cache = nullptr, *device_out = nullptr;
  uint64_t *device_table = nullptr;
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
  const uint64_t grid = lanes / block + (lanes % block != 0);
  if (grid > (uint64_t)properties.maxGridSize[0])
    return 1000 + (int)cudaErrorInvalidConfiguration;
  host_statuses = (int *)malloc(lanes * sizeof(int));
  if (!host_statuses) return 1000 + (int)cudaErrorMemoryAllocation;
#define CUDA_TRY(call) do { status = (call); if (status != cudaSuccess) goto done; } while (0)
  if (cache_length) {
    CUDA_TRY(cudaMalloc((void **)&device_cache, cache_length * sizeof(uint32_t)));
    CUDA_TRY(cudaMemcpy(device_cache, cache, cache_length * sizeof(uint32_t), cudaMemcpyHostToDevice));
  }
  if (table_length) {
    CUDA_TRY(cudaMalloc((void **)&device_table, table_length * sizeof(uint64_t)));
    CUDA_TRY(cudaMemcpy(device_table, table, table_length * sizeof(uint64_t), cudaMemcpyHostToDevice));
  }
  if (out_length) {
    CUDA_TRY(cudaMalloc((void **)&device_out, out_length * sizeof(uint32_t)));
    CUDA_TRY(cudaMemcpy(device_out, out, out_length * sizeof(uint32_t), cudaMemcpyHostToDevice));
  }
  CUDA_TRY(cudaMalloc((void **)&device_statuses, lanes * sizeof(int)));
  lowered_device<<<(unsigned)grid, block>>>(device_cache, cache_length, device_table,
      table_length, device_out, out_length, page_size, tokens, lanes, device_statuses);
  CUDA_TRY(cudaGetLastError());
  CUDA_TRY(cudaDeviceSynchronize());
  CUDA_TRY(cudaMemcpy(host_statuses, device_statuses, lanes * sizeof(int), cudaMemcpyDeviceToHost));
  if (out_length)
    CUDA_TRY(cudaMemcpy(out, device_out, out_length * sizeof(uint32_t), cudaMemcpyDeviceToHost));
  for (uint64_t lane = 0; lane < lanes; ++lane)
    if (host_statuses[lane]) { result = host_statuses[lane]; break; }
done:
  void *buffers[4] = { device_statuses, device_out, device_table, device_cache };
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
  laneBody code true ++ cudaWrapper

end Keystone.Lowering

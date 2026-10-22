# Keystone prototypes

Three small Lean 4 experiments around paged KV-cache access:

1. **GPU semantics:** prove a KV-gather kernel safe and correct under instruction interleavings.
2. **KV lifetimes:** keep pages allocated until every submitted operation completes.
3. **Verified lowering:** compile structured kernels into flat predicated instructions, preserving results and faults.

## Run

Install [Lean via elan](https://lean-lang.org/install/), Python 3.9+, Make, and a C compiler (`cc`).
Lean is pinned in `lean-toolchain`; there are no extra Lean or Python packages.

```sh
make demo           # small examples of all three prototypes
make check          # build, focused tests, axiom audit, demos
make lowering-demo  # just the compiler example
python3 -m experiments.lowering --source  # inspect emitted C
```

CPU execution is the default. Optional CUDA execution requires `nvcc` and an NVIDIA GPU:

```sh
python3 -m experiments.demo --cuda
python3 -m experiments.lowering --cuda
```

## Start here

Read definitions before proofs. The wrappers can wait.

| Topic | Definitions | Proofs / next step |
|---|---|---|
| GPU | [GPU/KVGather.lean](Keystone/GPU/KVGather.lean) | [Proofs.lean](Keystone/GPU/Proofs.lean), then [Progress.lean](Keystone/GPU/Progress.lean) |
| KV page lifetimes | [KV/Controller.lean](Keystone/KV/Controller.lean) | [Examples.lean](Keystone/KV/Examples.lean), then [Lifetime.lean](Keystone/KV/Lifetime.lean) |
| Lowering | [Lowering/Language.lean](Keystone/Lowering/Language.lean) | [Compiler.lean](Keystone/Lowering/Compiler.lean), then [Proofs.lean](Keystone/Lowering/Proofs.lean) |
| Connecting them | [Lowering/Gather.lean](Keystone/Lowering/Gather.lean) | [Composition.lean](Keystone/Composition.lean) |

`Keystone/CLI/` contains JSON entry points. `experiments/` contains the Python runners;
start with [demo.py](experiments/demo.py). `tests/` keeps a few regressions per prototype.
Generated native files live under `artifacts/`; Lean builds live under `.lake/`.

## The computation

Thread `tid` copies token `tid`'s entry out of the paged KV cache (page size `B`):

```text
output[tid] = kvCache[pageTable[tid / B] * B + tid % B]    if tid < numTokens
```

The GPU model implements this one KV-gather kernel, with explicit masking and indexing.
The KV model exposes a different failure: an in-bounds kernel can read another
request's data if a page is reused too early. The compiler proves that translating
a structured program to flat instructions preserves outputs, access traces,
faults, and stack frames.

All native demos share one path:

```text
Lean source kernel → proved lowering → flat IR → trusted C/CUDA emitter → native code
```

The controller runs the same Lean functions whose properties are proved.
`compile_correct` is the general lowering theorem; `pending_lowered_gather_correct`
connects live KV leases to the lowered gather.

## Try a change

- Change the page table in `kernel_demo`; predict the output before running it.
- Change the completion order in `lifetime_demo`; check when reuse becomes possible.
- Read the compiler, then add a source operation and work through its proof case.

## Mutation experiments

[tests/Mutations.lean](tests/Mutations.lean) changes copies of kernel syntax or
compiled instructions. The interpreters and gather specification stay fixed;
there are no mutation modes in the model or runners. `make test` checks concrete
counterexamples for missing guards, wrong indices, and broken predicate restoration.
A correct compiler preserves a source bug; it does not make that kernel correct.
Mutated target instructions are outside the compiler theorem's conclusion.
Run these examples alone with `lake env lean tests/Mutations.lean`.

## Proof boundary

The lowering proof is per thread and ends at the IR. Serialization, native compilers,
FFI, drivers, and hardware remain trusted. CUDA is implemented but untested locally;
its runner accepts only valid gather programs with disjoint writes.

The KV model assumes atomic host operations, truthful completion signals, and no
writes to submitted pages. Delayed work is simulated on the host; native calls use
private buffers. The gather copies one UInt32 entry per token; it is not attention
or a complete inference engine. `make audit` checks the principal theorems for
unexpected axioms. No proofs are admitted.

# Keystone: GPU model and compilation

`main` contains your grid-stride KV gather, its proofs, and a compiler for that
same kernel. `prototype-1` remains an older reference; its separate lowering
language is not the starting point here. Lean is pinned in `lean-toolchain`.

```sh
make check                                      # build everything; warnings fail
lake env lean Keystone/Compile/Compiler.lean     # check the file you are reading
```

Open the repository root in your Lean editor. Read in this order; paths below
are under `Keystone/`.

| File | What to understand |
| --- | --- |
| `GPU/KVGather.lean` | Thread state, memory, instruction execution, and schedules |
| `GPU/Properties.lean` | The five kernel guarantees; consult `Auxiliary.lean` for their proofs |
| `Compile/IR.lean` | Primitive register operations and their independent interpreter |
| `Compile/Compiler.lean` | How each existing GPU instruction becomes a target block |
| `Compile/Correctness.lean` | Step equivalence, schedule equivalence, and inherited guarantees |
| `Compile/Examples.lean` | Checked runs, faults, starvation, and a compiler mutation |
| `Compile/Emit.lean` | Trusted C serialization of those same compiled blocks |

## What connects the two layers

`Compile` imports the GPU model and uses its `Config`, `KVMemory`, `Thread`,
`KernelState`, `Access`, and `Fault` directly. It adds one temporary register.
The source program is the existing `GPU.Instr` stages; the compiler expands each
stage into arithmetic, checked reads/writes, and a branch or jump.

For example, `.page` becomes:

```text
temp        = round * numThreads
temp        = threadId + temp
logicalPage = temp / pageSize
jump to .table
```

The target interpreter executes these operations without calling `GPU.step`.
`step_eq` proves the block has exactly that GPU instruction's effect, including
faults, for arbitrary states and configurations. It converts the source's optional
access into a list. `run_eq` extends equality to every supplied schedule: the
complete kernel state, access trace, and fault result agree.

Consequently, the GPU proofs also establish target memory safety, completed-output
correctness, distinct stores, completion under sufficient scheduling, and verified
round-robin execution. Those properties retain their original assumptions.

## Concrete milestones

1. **Trace the source loop.** With 8 tokens and 5 threads, explain why thread 0
   handles tokens 0 and 5. Follow `.store` back to `.guard`; explain why padded
   threads stop without memory accesses. Check `GPU/Examples.lean`.
2. **Read the claims before their helpers.** Explain `ValidLaunch`, the invariant,
   and why completion needs scheduling. The sufficient bound is
   `6 * numRounds cfg + 1` turns per thread, not a fixed six turns.
3. **Trace a compiled block.** Follow `.page`, then `.kvIndex`, then `.store`.
   Predict every register, next GPU stage, and memory access before evaluating it.
4. **Follow the proof connection.** Read `step_eq`, then the schedule induction
   in `run_eq`. Pick one transferred GPU property and explain the rewrite.
5. **Break only the compiled syntax.** The example replaces division with remainder
   in the `.page` block. Observe the disagreement while leaving the interpreter
   and expected behavior unchanged.

Work one definition or lemma at a time: predict, edit, run `make check`, then
commit when you can explain the change. Import new modules from `Keystone.lean`.

## Scope and later steps

Each scheduled turn executes one complete target block. Jumps select the block
for that thread's next turn. The proof covers these block boundaries; it does not
cover arbitrary interleavings of operations inside a block. The proved model uses
`Nat` indices and `UInt32` payloads.

`Emit.lean` serializes the compiled blocks into C99. `kg_run` replays an explicit
thread schedule on the CPU. Its `uint64_t` arithmetic rejects overflow; buffers
must have their declared lengths, inputs remain immutable and separate from
output, and thread/output state starts at zero. On error, discard state and trace.
Serialization, machine-width arithmetic, and the C compiler/runtime are trusted;
there is no emitted-C theorem or CUDA execution claim.

```sh
lake exe emit_c > /tmp/keystone.c
cc -std=c99 -Wall -Wextra -Werror -c /tmp/keystone.c -o /tmp/keystone.o
lake exe emit_c --oracle  # source-model fixtures for native comparison
```

Next milestones: prove a machine-integer refinement or validate emitted code;
connect **KV lifetimes** to the kernel's assumption that pages remain unchanged.

Questions to explore: which scheduling granularity should a GPU semantics expose?
What completion event permits page reclamation? Should the final backend be
verified, translation-validated, or deliberately trusted?

[Architecture slide](architecture-slide/dist/index.html) is local only.
Open it in a browser; click or press → to reveal.

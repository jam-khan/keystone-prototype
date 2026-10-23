# Keystone Prototype/Ideation

`GPU/` models a kernel that gathers paged KV entries into token order.
`Compile/` translates its stages into register instructions and proves that execution
preserves the same state, memory accesses, and faults. `KV/` manages page ownership
and runs that compiled kernel against the shared cache, keeping pages allocated
until pending work finishes—even after cancellation.

Paths below are under `Keystone/`.

| File | Purpose |
| --- | --- |
| `GPU/KVGather.lean` | Kernel state, execution, schedules, and expected output |
| `Compile/Target.lean` | Target instructions and their interpreter |
| `Compile/Compiler.lean` | GPU stages → target instructions |
| `Compile/Emit.lean` | C code generation |
| `KV/Manager.lean` | Leases, tickets, allocation, and reclamation |
| `KV/Runtime.lean` | Shared cache, kernel launch, execution, and completion |

Each component has `Examples.lean` for concrete runs, `Properties.lean` for the
main guarantees, and `Proofs/` for supporting details. Skip `Proofs/` initially.

From the repository root, with Lean and Lake installed:

```sh
make check                                      # check proofs and examples
lake env lean Keystone/Compile/Compiler.lean     # check one file
lake exe emit_c > /tmp/keystone.c                # generate C
cc -std=c99 -Wall -Wextra -Werror -c /tmp/keystone.c -o /tmp/keystone.o
```

The generated C replays kernel schedules on the CPU; emission is trusted.

# Keystone: build it gradually

`main` is your working implementation. `prototype-1` holds the completed reference.
This branch starts with Lean 4.34.1, an empty GPU module, and no external packages.

## Start

```sh
make check                            # builds; warnings fail the check
lake env lean Keystone/GPU/Model.lean  # check the file you are editing
git show prototype-1:Keystone/GPU/Model.lean  # read the reference without switching
```

Open the repository root in your Lean editor. Start in `Keystone/GPU/Model.lean`.
As you add modules, import them from `Keystone.lean` so `make check` checks them.
The scaffold is ready for your first commit; nothing has been staged or committed.

## Milestones

Paths below are under `Keystone/`. Each milestone can be several small commits.
Use `prototype-1` to look up a definition or lemma when stuck, then explain it in
your own words before incorporating it.

1. **Specify paged gather — `GPU/Model.lean`.** Define `Config`, `Input`,
   `referenceAt`, and `reference`: `out[t] = cache[table[t / B] * B + t % B]`.
   **Done:** with `B=2`, `n=5`, `lanes=8`, table `#[2,0,1]`, and cache
   `#[10,11,20,21,30,31]`, a checked example returns `#[30,31,10,11,20]`.

2. **Execute instructions — `GPU/Model.lean`.** Add lane state, program counters,
   accesses, faults, `step`, and a schedule-driven `run`.
   **Done:** a complete schedule matches the specification; a starved lane stays
   incomplete; removing the mask or using the wrong page index exposes a failure.

3. **Prove safety and values — `GPU/Auxiliary.lean`, `GPU/Properties.lean`.** State `ValidInput` in the model;
   build `LaneOK` and `Invariant`, then `table_bounds`, `cache_bounds`, `step_safe`,
   `run_safe`, and `completed_execution_correct`.
   **Done:** explain why each memory access is bounded and why completed outputs
   match the specification for any schedule containing valid lane IDs.

4. **Prove completion — `GPU/Auxiliary.lean`, `GPU/Properties.lean`.** Track instructions remaining;
   prove `sufficiently_scheduled_finishes`, then `verified_roundRobin`.
   **Done:** six turns per lane suffice; explain why safety alone permits starvation.

5. **Model page lifetimes — `KV/Controller.lean`, `KV/Examples.lean`.** Implement
   leases, tickets, allocation, submission, retirement, and completion.
   **Done:** retire A with two readers pending; B cannot reuse A's page after just
   one completion, can after both, and a stale A completion cannot disturb B.

6. **Prove lifetime safety — `KV/Controller.lean`, `KV/Lifetime.lean`.** Establish
   `Valid` and preservation per command, then `run_valid`, `lifetime_safety`,
   non-reappearance of completed tickets/reclaimed leases, and final reclamation.
   **Done:** these claims hold for arbitrary histories; identify the assumptions
   about completion signals, request IDs, and writes to pending pages.

7. **Build a compiler — `Lowering/Language.lean`, `Lowering/Compiler.lean`.** Define
   structured source commands and a separate flat stack interpreter. Compile
   expressions to postfix instructions and guards to balanced predicate regions.
   **Done:** nested guards skip invalid reads and restore the enclosing predicate;
   source and target agree on output, access trace, and a fault's partial state.

8. **Prove the compiler — `Lowering/Proofs.lean`.** Start with `target_append` and
   `compileExpr_correct`; handle inactive execution, then prove `compile_correct`.
   **Done:** correctness holds for every source command and arbitrary caller stack
   and mask frames, including faults. A few equal example outputs are insufficient.

9. **Connect the models — `Lowering/Gather.lean`, `Composition.lean`.** Encode the
   gather, establish word-size bounds, derive its memory contract from live leases,
   and prove `pending_lowered_gather_correct`.
   **Done:** trace each premise from a pending ticket to the lowered result;
   distinguish retaining an allocation from preserving its contents.

10. **Run native code — `Lowering/Emit.lean`, then `CLI/` and `experiments/`.** Add
    C emission and a small runner; compare specification, both interpreters, and
    native output. Add focused regressions, an axiom audit, and CI as needed.
    **Done:** explain exactly where the proof ends. CUDA is an optional later step
    requiring hardware validation; emitted C/CUDA and drivers remain trusted.

## Working rhythm

Predict one example, implement one definition or lemma, then run `make check` and
commit that increment. Use `#eval` to inspect execution and `example ... := by decide`
for finite checked examples. State general properties as theorems; keep committed
proofs free of `sorry`. Suggested first commit: `chore: bootstrap Lean project`.

## Questions to carry into the interview

- **GPU semantics:** what semantic level should Keystone verify first, and which
  concurrency features—barriers, atomics, shared memory—are essential?
- **Runtime:** what event establishes that a cancelled request's pages are safe
  to reclaim across streams? Where should that obligation meet the driver API?
- **Extraction:** what should connect proved IR semantics to deployed kernels:
  a verified backend, translation validation, or a deliberately trusted compiler?

These experiments target the JD's kernel semantics, runtime glue, verified
artifacts, and trusted computing base. They are models for discussion, not a claim
that Keystone has chosen this architecture.

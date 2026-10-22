# Handoff

## User and working style
- Preparing for a Keystone (machine-verified LLM inference) software-engineer interview with Nate Foster. JD, CV, and loose paper references are in ignored `docs/`. Papers are inspiration, not project requirements.
- Wants substantive GPU semantics, verified lowering/extraction, and KV-cache lifetime prototypes. Avoid overstating guarantees.
- Now learning/rebuilding gradually on `main`, making their own commits. Explain one concept at a time, very concisely, with concrete examples and meaningful names. Preserve their comments and edits. No unsolicited large refactors, long READMEs, or extra tests.
- Do not commit, stage, push, or switch branches unless requested. Read current files/status before edits; user actively changes them between messages.

## Current repository state (2026-10-22)
- Workspace: `/Users/jamkabeeralikhan/Documents/Programming/keystone-prototype`.
- Checked out `main`: `7f81580` (`clean up of GPU model further`), ahead of origin/main by 4 commits.
- `Keystone/GPU/Model.lean` has uncommitted user edits. This handoff is newly added.
- `prototype-1`: `2c9a4bc` (`updated GPU kernel semantics`), matches origin/prototype-1; completed reference implementation.
- Lean pinned to `leanprover/lean4:v4.34.1`; installed locally. Python 3.9, C compiler available; CUDA execution not tested here.
- On main, `make check` runs `lake build --wfail`. Minimal library imports GPU/Model; README has ten learning milestones. No need to copy the full prototype into main.

## Reference branch
- GPU: small-step gather with explicit lane scheduling; proofs of bounds, output correctness, padded-lane silence, disjoint stores, and completion after sufficient scheduling.
- KV: leases (page/owner/generation), operation tickets, cancellation/retirement, delayed reclamation, stale completion protection, arbitrary-history proofs.
- Lowering: structured kernel DSL → flat stack/predicate IR. `compile_correct` preserves state, traces, faults and restores caller frames on success. Gather specialization and `Composition.lean` connect live leases to kernel bounds/results.
- One native C/CUDA backend, emitted from compiled IR. Proof ends at IR; emitter, serialization, native compiler, FFI, driver/hardware are trusted. KV assumes atomic commands, truthful completion, and sealed pending pages. Host delayed-work demo uses private native buffers.
- Last reference validation passed: Lean build, 14 Python tests, `tests/Mutations.lean`, 8 principal-theorem axiom audits, CPU demos.

## Important design correction already completed
- User rightly disliked embedding bugs as runtime modes (`Program.gather/missingMask/wrongPage`). Removed `Program`, mutation parameters, and branches from GPU `step`/`run`, and removed mutation options from both CLI runners. Updated dependent proofs.
- Mutations now live only in reference `tests/Mutations.lean`: change copies of source AST or compiled instructions while keeping interpreters/specification fixed. Tests demonstrate missing guards, wrong indices, and predicate-frame corruption.
- Compiler correctness can preserve a buggy source program; it does not establish that program implements gather. Arbitrarily altered target instructions are outside the compiler theorem. Describing behavior semantically does not certify correctness.
- Applied the clean single-kernel Model to main too, preserving user's comments. Reference and main now intentionally differ in comments/names.

## Current learning point / naming
- User has walked through Config, Input, PC, Lane, Machine, Space, Access, Fault, index calculation, and expected outputs.
- Example: pageSize=2, n=5, lanes=8, table `#[2,0,1]`, cache `#[10,11,20,21,30,31]` gives output `#[30,31,10,11,20]`; lanes 5–7 are inactive.
- `Space` names buffers, not CUDA memory-space categories. Addresses here are element indices. `output : Nat → Option UInt32` uses none for unwritten slots.
- Correct formula: `physicalPage input (tid / cfg.pageSize) * cfg.pageSize + tid % cfg.pageSize`. Extra parentheses putting multiplication/offset INSIDE physicalPage were an uncommitted main typo, never in prototype-1.
- Main renamed `gatherAddress` → `cacheIndex`. Concise formula comment added.
- Most recent discussion recommended `referenceAt` → `expectedValue`, `reference` → `expectedOutput`. Current file inspection confirms the user has ALREADY made these renames. Do not repeat or overwrite them.
- Reference branch retains old names. No cross-branch rename requested. Latest main edits have not been rebuilt in this handoff turn.
- Current `step` is mid-edit: it declares `let lane := m.threads tid` but still uses `l.pc` and `{ l with ... }` below. Likely an unfinished user rename; do not claim the current file builds. No correction made during this handoff-only request.

## Next agent
Continue answering the user's next specific learning question. Inspect current Model before editing; keep explanations short. Explicit action requests should be implemented and checked. No pending implementation request beyond writing this handoff.

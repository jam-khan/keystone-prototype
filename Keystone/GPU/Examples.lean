import Keystone.GPU.KVGather

/-!
Checked examples for the running KV-gather example.
`#guard` evaluates a `Bool` at build time; `make check` fails if any is `false`.
-/

namespace Keystone.GPU.Examples

open Keystone.GPU

private def cfg   : Config :=
  { numTokens  := 5,
    pageSize   := 2,
    numThreads := 8
  }
private def mem : KVMemory :=
  { pageTable := #[2, 0, 1],
    kvCache := #[10, 11, 20, 21, 30, 31]
  }

#guard validateLaunch cfg mem
#guard expectedOutput cfg mem == #[30, 31, 10, 11, 20]

-- every thread gets 6 turns: finishes and matches the spec
#guard match run cfg mem (roundRobin cfg) initialState with
  | .ok (s, _) => completed cfg s && outputEntries cfg s == (expectedOutput cfg mem).map some
  | .error _ => false

-- thread 4 never scheduled: unfinished, output slot 4 empty
#guard match run cfg mem (List.replicate 6 (List.range 4)).flatten initialState with
  | .ok (s, _) => !completed cfg s && s.output 4 == none
  | .error _ => false

-- order doesn't matter: run threads backwards (7, 6, …, 0), same output
#guard match run cfg mem (roundRobin cfg).reverse initialState with
  | .ok (s, _) => completed cfg s && outputEntries cfg s == (expectedOutput cfg mem).map some
  | .error _ => false

-- padded threads 5, 6, 7 never touch memory
#guard match run cfg mem (roundRobin cfg) initialState with
  | .ok (_, accesses) => accesses.all (fun a => a.thread < cfg.numTokens)
  | .error _ => false

-- bad page table: logical page 2 → physical page 7, but the KV cache has only pages 0–2
private def badMem : KVMemory := { mem with pageTable := #[2, 0, 7] }

#guard !validateLaunch cfg badMem
-- thread 4: page 2 → physical 7 → kvIndex 7 * 2 + 0 = 14 ≥ KV-cache size 6, so `.load` faults
#guard match run cfg badMem (roundRobin cfg) initialState with
  | .error fault => fault == .outOfBounds ⟨4, .kvCache, 14⟩
  | .ok _ => false

end Keystone.GPU.Examples

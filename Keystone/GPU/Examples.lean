import Keystone.GPU.Model

/-!
Checked examples for the running gather example.
`#guard` evaluates a `Bool` at build time; `make check` fails if any is `false`.
-/

namespace Keystone.GPU.Examples

open Keystone.GPU

private def cfg   : Config :=
  { numElements := 5,
    pageSize    := 2,
    numThreads := 8
  }
private def input : Input :=
  { pageTable := #[2, 0, 1],
    cache := #[10, 11, 20, 21, 30, 31]
  }

#guard validateInput  cfg input
#guard expectedOutput cfg input == #[30, 31, 10, 11, 20]

-- every thread gets 6 turns: finishes and matches the spec
#guard match run cfg input (roundRobin cfg) init with
  | .ok (m, _) => completed cfg m && outputValues cfg m == (expectedOutput cfg input).map some
  | .error _ => false

-- thread 4 never scheduled: unfinished, output slot 4 empty
#guard match run cfg input (List.replicate 6 (List.range 4)).flatten init with
  | .ok (m, _) => !completed cfg m && m.output 4 == none
  | .error _ => false

-- order doesn't matter: run threads backwards (7, 6, …, 0), same output
#guard match run cfg input (roundRobin cfg).reverse init with
  | .ok (m, _) => completed cfg m && outputValues cfg m == (expectedOutput cfg input).map some
  | .error _ => false

-- padded threads 5, 6, 7 never touch memory
#guard match run cfg input (roundRobin cfg) init with
  | .ok (_, accesses) => accesses.all (fun a => a.thread < cfg.numElements)
  | .error _ => false

-- bad page table: logical page 2 → physical page 7, but cache has only pages 0–2
private def badInput : Input := { input with pageTable := #[2, 0, 7] }

#guard !validateInput cfg badInput
-- thread 4: page 2 → physical 7 → address 7 * 2 + 0 = 14 ≥ cache size 6, so `.load` faults
#guard match run cfg badInput (roundRobin cfg) init with
  | .error fault => fault == .outOfBounds ⟨4, .cache, 14⟩
  | .ok _ => false

end Keystone.GPU.Examples

import Keystone.Compile.Compiler

namespace Keystone.Compile.Examples

open GPU

private def cfg : Config := { numTokens := 8, pageSize := 2, numThreads := 5 }
private def mem : KVMemory :=
  { pageTable := #[2, 0, 3, 1], kvCache := #[10, 11, 20, 21, 30, 31, 40, 41] }

-- Fewer threads than tokens: compiled stores advance the round and loop.
#guard match Compile.run cfg mem (roundRobin cfg) initialState,
    GPU.run cfg mem (roundRobin cfg) initialState with
  | .ok (target, targetAccesses), .ok (source, sourceAccesses) =>
      completed cfg target &&
      outputEntries cfg target == #[30, 31, 10, 11, 40, 41, 20, 21].map some &&
      outputEntries cfg target == outputEntries cfg source &&
      targetAccesses == sourceAccesses &&
      (List.range cfg.numThreads).all (fun tid => target.threads tid == source.threads tid)
  | _, _ => false

-- Reverse the interleaving: the same compiled kernel still finishes correctly.
#guard match Compile.run cfg mem (roundRobin cfg).reverse initialState with
  | .ok (s, _) => completed cfg s && outputEntries cfg s == (expectedOutput cfg mem).map some
  | .error _ => false

private def padded : Config := { cfg with numTokens := 5, numThreads := 8 }

-- Padded threads finish at the guard without touching any buffer.
#guard match Compile.run padded mem (roundRobin padded) initialState with
  | .ok (s, accesses) =>
      completed padded s &&
      outputEntries padded s == (expectedOutput padded mem).map some &&
      accesses.all (fun a => a.thread < padded.numTokens)
  | .error _ => false

-- Only thread 0 runs: it copies tokens 0 and 5, but cannot finish other threads.
#guard match Compile.run cfg mem (List.replicate 13 0) initialState with
  | .ok (s, _) =>
      !completed cfg s && (s.threads 0).instr == .done &&
      outputEntries cfg s == #[some 30, none, none, none, none, some 41, none, none]
  | .error _ => false

-- Faults retain the GPU model's exact thread, buffer, and index.
#guard match Compile.run padded { mem with pageTable := #[2, 0, 7] }
    (roundRobin padded) initialState with
  | .error fault => fault == .outOfBounds ⟨4, .kvCache, 14⟩
  | .ok _ => false

#guard match Compile.run padded mem [8] initialState with
  | .error fault => fault == .invalidThread 8
  | .ok _ => false

-- Mutate compiled syntax, keeping the interpreter and GPU semantics unchanged.
private def wrongPageBlock : List Instruction :=
  (compile .page).map fun op => match op with
    | .binary .div dest lhs rhs => .binary .mod dest lhs rhs
    | other => other

#guard match GPU.run cfg mem [1] initialState with
  | .error _ => false
  | .ok (start, _) =>
      match GPU.step cfg mem 1 start, executeBlock cfg mem 1 wrongPageBlock ⟨start, 0⟩ with
      | .ok (source, _), .ok (target, _) =>
          (source.threads 1).logicalPage == 0 && (target.kernel.threads 1).logicalPage == 1
      | _, _ => false

end Keystone.Compile.Examples

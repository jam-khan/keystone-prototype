import Keystone.GPU.Proofs
import Keystone.Lowering.Proofs

/-! Paged KV gather: word-size bounds, source correctness, and compiler application. -/
namespace Keystone.Lowering

/-- Bounds connecting natural-number indices to UInt64 arithmetic. -/
structure NativeBounds (cfg : GPU.Config) (mem : GPU.KVMemory) : Prop where
  numTokens : cfg.numTokens < UInt64.size
  pageSize : cfg.pageSize < UInt64.size
  numThreads : cfg.numThreads ≤ UInt64.size
  kvCache : mem.kvCache.size ≤ UInt64.size
  pages : ∀ p : Fin mem.pageTable.size, GPU.physicalPage mem p < UInt64.size

theorem word_ofNat (bound : n < UInt64.size) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' bound

/-- The KV-index calculation's multiplication and addition do not wrap. -/
theorem word_kvIndex (ht : tid < UInt64.size) (hb : pageSize < UInt64.size)
    (hp : page < UInt64.size)
    (hi : page * pageSize + tid % pageSize < UInt64.size) :
    (UInt64.ofNat page * UInt64.ofNat pageSize +
      UInt64.ofNat tid % UInt64.ofNat pageSize).toNat =
      page * pageSize + tid % pageSize := by
  have hm : page * pageSize < UInt64.size := by omega
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod,
    word_ofNat ht, word_ofNat hb, word_ofNat hp]
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hi]

theorem gather_word_kvIndex (valid : GPU.ValidLaunch cfg mem)
    (bounds : NativeBounds cfg mem) (active : tid < cfg.numTokens) :
    (UInt64.ofNat (GPU.physicalPage mem (tid / cfg.pageSize)) *
      UInt64.ofNat cfg.pageSize + UInt64.ofNat tid % UInt64.ofNat cfg.pageSize).toNat =
      GPU.kvIndex cfg mem tid := by
  apply word_kvIndex
  · exact Nat.lt_trans active bounds.numTokens
  · exact bounds.pageSize
  · exact bounds.pages ⟨tid / cfg.pageSize, GPU.table_bounds valid active⟩
  · exact Nat.lt_of_lt_of_le (GPU.kvCache_bounds valid active) bounds.kvCache

/-- Locals 0–3 hold the logical page, physical page, KV index, and entry. -/
def gather : Cmd :=
  .whenLt (.arg .tid) (.arg .numTokens)
    (.seq (.set 0 (.bin .div (.arg .tid) (.arg .pageSize)))
    (.seq (.loadPageTable 1 (.local 0))
    (.seq (.set 2 (.bin .add (.bin .mul (.local 1) (.arg .pageSize))
                             (.bin .mod (.arg .tid) (.arg .pageSize))))
    (.seq (.loadKVCache 3 (.local 2))
           (.store (.arg .tid) (.local 3))))))

def gatherContext (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat) : Context :=
  ⟨UInt64.ofNat tid, UInt64.ofNat cfg.numTokens, UInt64.ofNat cfg.pageSize,
   mem.pageTable.map UInt64.ofNat, mem.kvCache⟩

def gatherEvents (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat) : List Access :=
  [⟨UInt64.ofNat tid, .pageTable, UInt64.ofNat (tid / cfg.pageSize)⟩,
   ⟨UInt64.ofNat tid, .kvCache, UInt64.ofNat (GPU.kvIndex cfg mem tid)⟩,
   ⟨UInt64.ofNat tid, .output, UInt64.ofNat tid⟩]

private def gatherFinal (cfg : GPU.Config) (mem : GPU.KVMemory) (tid : Nat) (state : State) : State :=
  let ctx := gatherContext cfg mem tid
  let logical := UInt64.ofNat (tid / cfg.pageSize)
  let physical := UInt64.ofNat (GPU.physicalPage mem (tid / cfg.pageSize))
  let index := UInt64.ofNat (GPU.kvIndex cfg mem tid)
  let entry := (GPU.expectedEntry cfg mem tid).toUInt64
  let s1 := setLocal state 0 logical
  let s2 := setLocal (record ctx s1 .pageTable logical) 1 physical
  let s3 := setLocal s2 2 index
  let s4 := setLocal (record ctx s3 .kvCache index) 3 entry
  { record ctx s4 .output (UInt64.ofNat tid) with
    output := fun j => if j = tid then GPU.expectedEntry cfg mem tid else state.output j }

private theorem word_div (ht : tid < UInt64.size) (hb : pageSize < UInt64.size) :
    UInt64.ofNat tid / UInt64.ofNat pageSize = UInt64.ofNat (tid / pageSize) := by
  apply UInt64.toNat_inj.mp
  have hi : tid / pageSize < UInt64.size := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ht
  simp only [UInt64.toNat_div, word_ofNat ht, word_ofNat hb, word_ofNat hi]

private theorem gather_source_active (valid : GPU.ValidLaunch cfg mem)
    (bounds : NativeBounds cfg mem) (active : tid < cfg.numTokens) (state : State) :
    source gather (gatherContext cfg mem tid) state =
      .ok (gatherFinal cfg mem tid state) := by
  have ht : tid < UInt64.size := Nat.lt_trans active bounds.numTokens
  have logicalBound : tid / cfg.pageSize < UInt64.size :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ht
  have indexBound : GPU.kvIndex cfg mem tid < UInt64.size :=
    Nat.lt_of_lt_of_le (GPU.kvCache_bounds valid active) bounds.kvCache
  have activeWord : UInt64.ofNat tid < UInt64.ofNat cfg.numTokens := by
    rw [UInt64.lt_iff_toNat_lt, word_ofNat ht, word_ofNat bounds.numTokens]
    exact active
  have logicalEq := word_div ht bounds.pageSize
  have indexEq : UInt64.ofNat (GPU.physicalPage mem (tid / cfg.pageSize)) *
      UInt64.ofNat cfg.pageSize + UInt64.ofNat tid % UInt64.ofNat cfg.pageSize =
      UInt64.ofNat (GPU.kvIndex cfg mem tid) := by
    apply UInt64.toNat_inj.mp
    rw [gather_word_kvIndex valid bounds active, word_ofNat indexBound]
  have indexEq' : UInt64.ofNat (mem.pageTable[tid / cfg.pageSize]'(GPU.table_bounds valid active)) *
      UInt64.ofNat cfg.pageSize + UInt64.ofNat tid % UInt64.ofNat cfg.pageSize =
      UInt64.ofNat (GPU.kvIndex cfg mem tid) := by
    simpa [GPU.physicalPage, getElem!_pos, GPU.table_bounds valid active] using indexEq

  simp [Except.bind, Except.map, gather, source, Expr.eval, getArg, applyOp, gatherContext,
    activeWord, logicalEq, readPageTable, word_ofNat logicalBound,
    Array.size_map, GPU.table_bounds valid active, setLocal,
    indexEq', GPU.physicalPage, readKVCache, word_ofNat indexBound, GPU.kvCache_bounds valid active,
    writeOutput, word_ofNat ht, gatherFinal, record, GPU.expectedEntry]

/-- Real threads return the expected entry with three accesses; padded threads are silent. -/
theorem gather_source_correct (valid : GPU.ValidLaunch cfg mem)
    (bounds : NativeBounds cfg mem) (launched : tid < cfg.numThreads) (state : State) :
    ∃ final, source gather (gatherContext cfg mem tid) state = .ok final ∧
      final.output = (fun j => if tid < cfg.numTokens ∧ j = tid
        then GPU.expectedEntry cfg mem tid else state.output j) ∧
      final.trace = state.trace ++
        (if tid < cfg.numTokens then gatherEvents cfg mem tid else []) := by
  by_cases active : tid < cfg.numTokens
  · refine ⟨gatherFinal cfg mem tid state, gather_source_active valid bounds active state, ?_, ?_⟩
    · simp only [gatherFinal, active, true_and]
    · simp [gatherFinal, gatherEvents, record, setLocal, active, gatherContext, List.append_assoc]
  · have ht : tid < UInt64.size := Nat.lt_of_lt_of_le launched bounds.numThreads
    have inactiveWord : ¬ UInt64.ofNat tid < UInt64.ofNat cfg.numTokens := by
      rw [UInt64.lt_iff_toNat_lt, word_ofNat ht, word_ofNat bounds.numTokens]
      exact active
    refine ⟨state, ?_, ?_, ?_⟩
    · simp [gather, source, Expr.eval, getArg, gatherContext, inactiveWord]
    · simp [active]
    · simp [active]

/-- Apply the general compiler theorem to gather, preserving both caller frames. -/
theorem gather_target_correct (valid : GPU.ValidLaunch cfg mem)
    (bounds : NativeBounds cfg mem) (launched : tid < cfg.numThreads) (state : State)
    (stack : List UInt64) (masks : List Bool) :
    ∃ final, target (compile gather) (gatherContext cfg mem tid)
        ⟨state, stack, true, masks⟩ = .ok ⟨final, stack, true, masks⟩ ∧
      final.output = (fun j => if tid < cfg.numTokens ∧ j = tid
        then GPU.expectedEntry cfg mem tid else state.output j) ∧
      final.trace = state.trace ++
        (if tid < cfg.numTokens then gatherEvents cfg mem tid else []) := by
  obtain ⟨final, execution, output, trace⟩ := gather_source_correct valid bounds launched state
  refine ⟨final, ?_, output, trace⟩
  rw [compile_correct, execution]
  rfl

end Keystone.Lowering

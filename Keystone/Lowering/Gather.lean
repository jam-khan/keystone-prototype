import Keystone.GPU.Proofs
import Keystone.Lowering.Proofs

/-! Paged gather: word-address bounds, source correctness, and compiler application. -/
namespace Keystone.Lowering

/-- Bounds connecting natural-number indices to UInt64 addressing. -/
structure NativeBounds (cfg : GPU.Config) (input : GPU.Input) : Prop where
  tokens : cfg.n < UInt64.size
  pageSize : cfg.pageSize < UInt64.size
  lanes : cfg.lanes ≤ UInt64.size
  cache : input.cache.size ≤ UInt64.size
  pages : ∀ p : Fin input.pageTable.size, GPU.physicalPage input p < UInt64.size

theorem word_ofNat (bound : n < UInt64.size) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' bound

/-- The address calculation’s multiplication and addition do not wrap. -/
theorem word_address (ht : tid < UInt64.size) (hb : pageSize < UInt64.size)
    (hp : page < UInt64.size)
    (ha : page * pageSize + tid % pageSize < UInt64.size) :
    (UInt64.ofNat page * UInt64.ofNat pageSize +
      UInt64.ofNat tid % UInt64.ofNat pageSize).toNat =
      page * pageSize + tid % pageSize := by
  have hm : page * pageSize < UInt64.size := by omega
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mod,
    word_ofNat ht, word_ofNat hb, word_ofNat hp]
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha]

theorem gather_word_address (valid : GPU.ValidInput cfg input)
    (bounds : NativeBounds cfg input) (active : tid < cfg.n) :
    (UInt64.ofNat (GPU.physicalPage input (tid / cfg.pageSize)) *
      UInt64.ofNat cfg.pageSize + UInt64.ofNat tid % UInt64.ofNat cfg.pageSize).toNat =
      GPU.gatherAddress cfg input tid := by
  apply word_address
  · exact Nat.lt_trans active bounds.tokens
  · exact bounds.pageSize
  · exact bounds.pages ⟨tid / cfg.pageSize, GPU.table_bounds valid active⟩
  · exact Nat.lt_of_lt_of_le (GPU.cache_bounds valid active) bounds.cache

/-- Locals 0–3 hold the logical page, physical page, address, and payload. -/
def gather : Cmd :=
  .whenLt (.arg .lane) (.arg .tokens)
    (.seq (.set 0 (.bin .div (.arg .lane) (.arg .pageSize)))
    (.seq (.loadTable 1 (.local 0))
    (.seq (.set 2 (.bin .add (.bin .mul (.local 1) (.arg .pageSize))
                             (.bin .mod (.arg .lane) (.arg .pageSize))))
    (.seq (.loadCache 3 (.local 2))
           (.store (.arg .lane) (.local 3))))))

def gatherContext (cfg : GPU.Config) (input : GPU.Input) (tid : Nat) : Context :=
  ⟨UInt64.ofNat tid, UInt64.ofNat cfg.n, UInt64.ofNat cfg.pageSize,
   input.pageTable.map UInt64.ofNat, input.cache⟩

def gatherEvents (cfg : GPU.Config) (input : GPU.Input) (tid : Nat) : List Access :=
  [⟨UInt64.ofNat tid, .table, UInt64.ofNat (tid / cfg.pageSize)⟩,
   ⟨UInt64.ofNat tid, .cache, UInt64.ofNat (GPU.gatherAddress cfg input tid)⟩,
   ⟨UInt64.ofNat tid, .output, UInt64.ofNat tid⟩]

private def gatherFinal (cfg : GPU.Config) (input : GPU.Input) (tid : Nat) (state : State) : State :=
  let ctx := gatherContext cfg input tid
  let logical := UInt64.ofNat (tid / cfg.pageSize)
  let physical := UInt64.ofNat (GPU.physicalPage input (tid / cfg.pageSize))
  let address := UInt64.ofNat (GPU.gatherAddress cfg input tid)
  let value := (GPU.referenceAt cfg input tid).toUInt64
  let s1 := setLocal state 0 logical
  let s2 := setLocal (record ctx s1 .table logical) 1 physical
  let s3 := setLocal s2 2 address
  let s4 := setLocal (record ctx s3 .cache address) 3 value
  { record ctx s4 .output (UInt64.ofNat tid) with
    output := fun j => if j = tid then GPU.referenceAt cfg input tid else state.output j }

private theorem word_div (ht : tid < UInt64.size) (hb : pageSize < UInt64.size) :
    UInt64.ofNat tid / UInt64.ofNat pageSize = UInt64.ofNat (tid / pageSize) := by
  apply UInt64.toNat_inj.mp
  have hi : tid / pageSize < UInt64.size := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ht
  simp only [UInt64.toNat_div, word_ofNat ht, word_ofNat hb, word_ofNat hi]

private theorem gather_source_active (valid : GPU.ValidInput cfg input)
    (bounds : NativeBounds cfg input) (active : tid < cfg.n) (state : State) :
    source gather (gatherContext cfg input tid) state =
      .ok (gatherFinal cfg input tid state) := by
  have ht : tid < UInt64.size := Nat.lt_trans active bounds.tokens
  have logicalBound : tid / cfg.pageSize < UInt64.size :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ht
  have addressBound : GPU.gatherAddress cfg input tid < UInt64.size :=
    Nat.lt_of_lt_of_le (GPU.cache_bounds valid active) bounds.cache
  have activeWord : UInt64.ofNat tid < UInt64.ofNat cfg.n := by
    rw [UInt64.lt_iff_toNat_lt, word_ofNat ht, word_ofNat bounds.tokens]
    exact active
  have logicalEq := word_div ht bounds.pageSize
  have addressEq : UInt64.ofNat (GPU.physicalPage input (tid / cfg.pageSize)) *
      UInt64.ofNat cfg.pageSize + UInt64.ofNat tid % UInt64.ofNat cfg.pageSize =
      UInt64.ofNat (GPU.gatherAddress cfg input tid) := by
    apply UInt64.toNat_inj.mp
    rw [gather_word_address valid bounds active, word_ofNat addressBound]
  have addressEq' : UInt64.ofNat (input.pageTable[tid / cfg.pageSize]'(GPU.table_bounds valid active)) *
      UInt64.ofNat cfg.pageSize + UInt64.ofNat tid % UInt64.ofNat cfg.pageSize =
      UInt64.ofNat (GPU.gatherAddress cfg input tid) := by
    simpa [GPU.physicalPage, getElem!_pos, GPU.table_bounds valid active] using addressEq

  simp [Except.bind, Except.map, gather, source, Expr.eval, getArg, applyOp, gatherContext,
    activeWord, logicalEq, readTable, word_ofNat logicalBound,
    Array.size_map, GPU.table_bounds valid active, setLocal,
    addressEq', GPU.physicalPage, readCache, word_ofNat addressBound, GPU.cache_bounds valid active,
    writeOutput, word_ofNat ht, gatherFinal, record, GPU.referenceAt]

/-- Active lanes return the gather value with three accesses; padded lanes are silent. -/
theorem gather_source_correct (valid : GPU.ValidInput cfg input)
    (bounds : NativeBounds cfg input) (launched : tid < cfg.lanes) (state : State) :
    ∃ final, source gather (gatherContext cfg input tid) state = .ok final ∧
      final.output = (fun j => if tid < cfg.n ∧ j = tid
        then GPU.referenceAt cfg input tid else state.output j) ∧
      final.trace = state.trace ++ (if tid < cfg.n then gatherEvents cfg input tid else []) := by
  by_cases active : tid < cfg.n
  · refine ⟨gatherFinal cfg input tid state, gather_source_active valid bounds active state, ?_, ?_⟩
    · simp only [gatherFinal, active, true_and]
    · simp [gatherFinal, gatherEvents, record, setLocal, active, gatherContext, List.append_assoc]
  · have ht : tid < UInt64.size := Nat.lt_of_lt_of_le launched bounds.lanes
    have inactiveWord : ¬ UInt64.ofNat tid < UInt64.ofNat cfg.n := by
      rw [UInt64.lt_iff_toNat_lt, word_ofNat ht, word_ofNat bounds.tokens]
      exact active
    refine ⟨state, ?_, ?_, ?_⟩
    · simp [gather, source, Expr.eval, getArg, gatherContext, inactiveWord]
    · simp [active]
    · simp [active]

/-- Apply the general compiler theorem to gather, preserving both caller frames. -/
theorem gather_target_correct (valid : GPU.ValidInput cfg input)
    (bounds : NativeBounds cfg input) (launched : tid < cfg.lanes) (state : State)
    (stack : List UInt64) (masks : List Bool) :
    ∃ final, target (compile gather) (gatherContext cfg input tid)
        ⟨state, stack, true, masks⟩ = .ok ⟨final, stack, true, masks⟩ ∧
      final.output = (fun j => if tid < cfg.n ∧ j = tid
        then GPU.referenceAt cfg input tid else state.output j) ∧
      final.trace = state.trace ++ (if tid < cfg.n then gatherEvents cfg input tid else []) := by
  obtain ⟨final, execution, output, trace⟩ := gather_source_correct valid bounds launched state
  refine ⟨final, ?_, output, trace⟩
  rw [compile_correct, execution]
  rfl

end Keystone.Lowering

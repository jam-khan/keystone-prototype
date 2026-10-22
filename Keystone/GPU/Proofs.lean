import Keystone.GPU.Model

namespace Keystone.GPU

/-- A real thread's `.table` read is inside the page table. -/
theorem table_bounds
  (h : ValidInput cfg input)
  (ht : tid < cfg.numElements)
    : tid / cfg.pageSize < input.pageTable.size := by
  unfold ValidInput at h
  -- h : 0 < pageSize ∧ numElements ≤ numThreads ∧ numElements ≤ pageTable.size * pageSize ∧ ∀ p, …
  -- name the four conjuncts in order (`_` prefix = unused here)
  obtain ⟨hpos, _hthreads, hcapacity, _hpages⟩ := h
  -- numElements ≤ pageTable.size * pageSize, so tid < pageTable.size * pageSize
  have h1 : tid < input.pageTable.size * cfg.pageSize := Nat.lt_of_lt_of_le ht hcapacity
  -- divide both sides by pageSize (> 0)
  exact (Nat.div_lt_iff_lt_mul hpos).mpr h1

/-- A real thread's `.load` read is inside the cache. -/
theorem cache_bounds
  (h : ValidInput cfg input)
  (ht : tid < cfg.numElements)
    : cacheIndex cfg input tid < input.cache.size := by
  sorry
  -- the logical page is a valid page-table position (previous theorem)
  -- have hlogical := table_bounds h ht
  -- unfold ValidInput at h
  -- obtain ⟨hpos, _hthreads, _hcapacity, hpages⟩ := h
  -- -- this thread's physical page fits in the cache: page start + pageSize ≤ cache.size
  -- have hfits := hpages ⟨tid / cfg.pageSize, hlogical⟩
  -- -- offset within the page is < pageSize
  -- have hoffset : tid % cfg.pageSize < cfg.pageSize := Nat.mod_lt tid hpos
  -- -- page start + offset < page start + pageSize ≤ cache.size
  -- unfold cacheIndex
  -- -- turn `↑⟨tid / pageSize, _⟩` in hfits into plain `tid / pageSize`
  -- simp only at hfits
  -- omega

end Keystone.GPU

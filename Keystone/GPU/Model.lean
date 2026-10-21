import Std

namespace Keystone.GPU

/--
  Shape of a gather launch

  Example `{ n := 5, pageSize := 2, lanes := 8 }`:
  - Lanes 0–4 gather elements; padded lanes 5–7 skip memory accesses.
  - Element 3 is in logical page `3 / 2 = 1`, at offset `3 % 2 = 1`.
    The page table maps logical pages to physical cache pages.
-/
structure Config where
  n         : Nat -- number of logical elements to gather
  pageSize  : Nat -- number of elements in each cache page
  lanes     : Nat -- number of launched GPU threads, including padding
  deriving Repr, DecidableEq

structure Input where
  pageTable   : Array Nat
  cache       : Array UInt32
  deriving Repr, DecidableEq

end Keystone.GPU

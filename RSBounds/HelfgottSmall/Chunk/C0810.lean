import RSBounds.HelfgottSmall.States

/-! Walk chunk 810, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottSmall.chunk_810 : RSBounds.HelfgottSmall.ChunkGood 810 := by
  decide +kernel

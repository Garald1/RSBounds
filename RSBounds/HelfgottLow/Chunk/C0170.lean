import RSBounds.HelfgottLow.States

/-! Walk chunk 170, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_170 : RSBounds.HelfgottLow.ChunkGood 170 := by
  decide +kernel

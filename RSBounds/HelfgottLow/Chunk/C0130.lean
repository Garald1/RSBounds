import RSBounds.HelfgottLow.States

/-! Walk chunk 130, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_130 : RSBounds.HelfgottLow.ChunkGood 130 := by
  decide +kernel

import RSBounds.HelfgottLow.States

/-! Walk chunk 95, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_95 : RSBounds.HelfgottLow.ChunkGood 95 := by
  decide +kernel

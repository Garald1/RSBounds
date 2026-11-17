import RSBounds.HelfgottLow.States

/-! Walk chunk 50, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_50 : RSBounds.HelfgottLow.ChunkGood 50 := by
  decide +kernel

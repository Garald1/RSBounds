import RSBounds.HelfgottLow.States

/-! Walk chunk 85, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_85 : RSBounds.HelfgottLow.ChunkGood 85 := by
  decide +kernel

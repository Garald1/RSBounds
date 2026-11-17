import RSBounds.HelfgottLow.States

/-! Walk chunk 180, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_180 : RSBounds.HelfgottLow.ChunkGood 180 := by
  decide +kernel

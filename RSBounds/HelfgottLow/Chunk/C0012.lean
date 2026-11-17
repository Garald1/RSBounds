import RSBounds.HelfgottLow.States

/-! Walk chunk 12, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_12 : RSBounds.HelfgottLow.ChunkGood 12 := by
  decide +kernel

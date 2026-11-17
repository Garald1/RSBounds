import RSBounds.HelfgottLow.States

/-! Walk chunk 30, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_30 : RSBounds.HelfgottLow.ChunkGood 30 := by
  decide +kernel

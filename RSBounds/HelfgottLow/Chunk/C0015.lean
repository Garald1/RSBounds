import RSBounds.HelfgottLow.States

/-! Walk chunk 15, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_15 : RSBounds.HelfgottLow.ChunkGood 15 := by
  decide +kernel

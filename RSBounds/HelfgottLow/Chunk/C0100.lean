import RSBounds.HelfgottLow.States

/-! Walk chunk 100, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_100 : RSBounds.HelfgottLow.ChunkGood 100 := by
  decide +kernel

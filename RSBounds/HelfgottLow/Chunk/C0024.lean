import RSBounds.HelfgottLow.States

/-! Walk chunk 24, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_24 : RSBounds.HelfgottLow.ChunkGood 24 := by
  decide +kernel

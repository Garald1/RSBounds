import RSBounds.HelfgottLow.States

/-! Walk chunk 122, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_122 : RSBounds.HelfgottLow.ChunkGood 122 := by
  decide +kernel

import RSBounds.HelfgottLow.States

/-! Walk chunk 1, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_1 : RSBounds.HelfgottLow.ChunkGood 1 := by
  decide +kernel

import RSBounds.HelfgottLow.States

/-! Walk chunk 4, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_4 : RSBounds.HelfgottLow.ChunkGood 4 := by
  decide +kernel

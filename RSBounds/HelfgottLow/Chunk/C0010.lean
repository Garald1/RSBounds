import RSBounds.HelfgottLow.States

/-! Walk chunk 10, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_10 : RSBounds.HelfgottLow.ChunkGood 10 := by
  decide +kernel

import RSBounds.HelfgottLow.States

/-! Walk chunk 5, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_5 : RSBounds.HelfgottLow.ChunkGood 5 := by
  decide +kernel

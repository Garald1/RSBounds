import RSBounds.HelfgottLow.States

/-! Walk chunk 13, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_13 : RSBounds.HelfgottLow.ChunkGood 13 := by
  decide +kernel

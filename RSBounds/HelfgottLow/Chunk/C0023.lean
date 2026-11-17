import RSBounds.HelfgottLow.States

/-! Walk chunk 23, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_23 : RSBounds.HelfgottLow.ChunkGood 23 := by
  decide +kernel

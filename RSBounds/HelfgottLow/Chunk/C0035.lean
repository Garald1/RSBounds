import RSBounds.HelfgottLow.States

/-! Walk chunk 35, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_35 : RSBounds.HelfgottLow.ChunkGood 35 := by
  decide +kernel

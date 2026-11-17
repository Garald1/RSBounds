import RSBounds.HelfgottLow.States

/-! Walk chunk 6, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_6 : RSBounds.HelfgottLow.ChunkGood 6 := by
  decide +kernel

import RSBounds.HelfgottLow.States

/-! Walk chunk 8, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_8 : RSBounds.HelfgottLow.ChunkGood 8 := by
  decide +kernel

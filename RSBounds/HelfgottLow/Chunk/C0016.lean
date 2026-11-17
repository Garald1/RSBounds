import RSBounds.HelfgottLow.States

/-! Walk chunk 16, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_16 : RSBounds.HelfgottLow.ChunkGood 16 := by
  decide +kernel

import RSBounds.HelfgottLow.States

/-! Walk chunk 70, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_70 : RSBounds.HelfgottLow.ChunkGood 70 := by
  decide +kernel

import RSBounds.HelfgottLow.States

/-! Walk chunk 45, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_45 : RSBounds.HelfgottLow.ChunkGood 45 := by
  decide +kernel

import RSBounds.HelfgottLow.States

/-! Walk chunk 120, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_120 : RSBounds.HelfgottLow.ChunkGood 120 := by
  decide +kernel

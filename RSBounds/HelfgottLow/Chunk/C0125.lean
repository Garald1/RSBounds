import RSBounds.HelfgottLow.States

/-! Walk chunk 125, checked by the kernel (one chunk per module, to bound memory). -/

theorem RSBounds.HelfgottLow.chunk_125 : RSBounds.HelfgottLow.ChunkGood 125 := by
  decide +kernel
